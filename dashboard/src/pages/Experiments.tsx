import { CheckCircle2, Download, ExternalLink, FileUp, Save, ShieldAlert, Trash2 } from "lucide-react";
import { useMemo, useState } from "react";
import { downloadText, extractVerdict, formatNumber, formatPercent, parseImportedRuns } from "../lib";
import type { DashboardData, ImportedRun } from "../types";

const DEFAULT_PROMPT = `You are deciding implication between two equational laws over all magmas.

Equation 1: {{equation1}}
Equation 2: {{equation2}}

Use the compact mathematical notes below. End with exactly VERDICT: TRUE or VERDICT: FALSE.

CHEATSHEET
- Track variable loss, projection, constant, commutative, and associative consequences.
- Prefer a direct derivation for TRUE and a small countermodel pattern for FALSE.
`;

interface PromptVersion {
  id: string;
  name: string;
  createdAt: string;
  prompt: string;
  model: string;
  dataset: string;
  tokenCap: number;
}

function readVersions(key: string): PromptVersion[] {
  try { return JSON.parse(localStorage.getItem(key) ?? "[]") as PromptVersion[]; }
  catch { return []; }
}

export default function Experiments({ data }: { data: DashboardData }) {
  const promptKey = `pibase-experiment-prompt:${data.source.commit}`;
  const versionsKey = "pibase-experiment-versions:v1";
  const [prompt, setPrompt] = useState(() => localStorage.getItem(promptKey) ?? DEFAULT_PROMPT);
  const [versionName, setVersionName] = useState("baseline");
  const [model, setModel] = useState(data.experiments.models[0]);
  const [dataset, setDataset] = useState(data.experiments.datasets[0]);
  const [tokenCap, setTokenCap] = useState(data.experiments.tokenCaps[0]);
  const [versions, setVersions] = useState<PromptVersion[]>(() => readVersions(versionsKey));
  const [runs, setRuns] = useState<ImportedRun[]>([]);
  const [runError, setRunError] = useState("");
  const [verdictText, setVerdictText] = useState("VERDICT: TRUE");
  const bytes = new TextEncoder().encode(prompt).length;
  const estimatedTokens = Math.ceil(prompt.length / 4);
  const missing = data.experiments.requiredPlaceholders.filter(
    (name) => !new RegExp(`\\{\\{\\s*${name}\\s*\\}\\}`, "i").test(prompt),
  );
  const parsedVerdict = extractVerdict(verdictText);
  const renderedPrompt = prompt
    .replace(/\{\{\s*equation1\s*\}\}/gi, "x * y = y * x")
    .replace(/\{\{\s*equation2\s*\}\}/gi, "(x * y) * z = (x * z) * y");

  const metrics = useMemo(() => {
    const normalized = runs.map((row) => {
      const verdict = row.verdict ?? extractVerdict(row.response_text ?? "");
      const correct = typeof row.correct === "boolean"
        ? row.correct
        : typeof row.expected_answer === "boolean" && verdict !== null
          ? row.expected_answer === verdict
          : null;
      return { ...row, verdict, correct };
    });
    const decided = normalized.filter((row) => row.correct !== null);
    const positive = normalized.filter((row) => row.expected_answer === true);
    const negative = normalized.filter((row) => row.expected_answer === false);
    const tokenRows = normalized.filter((row) => typeof row.tokens_out === "number");
    return {
      total: normalized.length,
      parseable: normalized.filter((row) => row.verdict !== null).length,
      correct: decided.filter((row) => row.correct).length,
      decided: decided.length,
      trueCorrect: positive.filter((row) => row.correct).length,
      trueTotal: positive.length,
      falseCorrect: negative.filter((row) => row.correct).length,
      falseTotal: negative.length,
      avgTokens: tokenRows.length
        ? Math.round(tokenRows.reduce((sum, row) => sum + (row.tokens_out ?? 0), 0) / tokenRows.length)
        : 0,
    };
  }, [runs]);

  function persistPrompt(next: string) {
    setPrompt(next);
    localStorage.setItem(promptKey, next);
  }

  function saveVersion() {
    const next: PromptVersion = {
      id: crypto.randomUUID(),
      name: versionName.trim() || `version-${versions.length + 1}`,
      createdAt: new Date().toISOString(),
      prompt,
      model,
      dataset,
      tokenCap,
    };
    const all = [next, ...versions];
    setVersions(all);
    localStorage.setItem(versionsKey, JSON.stringify(all));
  }

  function removeVersion(id: string) {
    const next = versions.filter((item) => item.id !== id);
    setVersions(next);
    localStorage.setItem(versionsKey, JSON.stringify(next));
  }

  async function importRuns(file: File | undefined) {
    if (!file) return;
    try {
      setRuns(parseImportedRuns(await file.text()));
      setRunError("");
    } catch (error) {
      setRunError(error instanceof Error ? error.message : "Could not parse run results");
    }
  }

  function exportVersion() {
    downloadText("equational-experiment.json", JSON.stringify({
      schemaVersion: 1,
      name: versionName,
      prompt,
      model,
      dataset,
      tokenCap,
      bytes,
      sourceCommit: data.source.commit,
    }, null, 2));
  }

  return (
    <div className="page experiments-page">
      <header className="page-intro compact-intro">
        <div>
          <p className="eyebrow">Upcoming equational-theories project</p>
          <h1>Prompt evaluation lab</h1>
          <p className="page-lede">
            Develop compact prompts that ask a model whether one equational law implies another, then compare
            accuracy across challenge datasets. This workspace is independent of the π-Base topology graph.
          </p>
          <a
            className="text-link experiment-context-link"
            href="https://competition.sair.foundation/competitions/mathematics-distillation-challenge-equational-theories-stage1/overview"
          >
            Mathematics Distillation Challenge <ExternalLink size={13} aria-hidden="true" />
          </a>
        </div>
        <div className={`budget-chip ${bytes > data.experiments.promptByteLimit ? "over-budget" : ""}`}>
          <small>Prompt budget</small>
          <strong>{formatNumber(bytes)}</strong>
          <span>/ {formatNumber(data.experiments.promptByteLimit)} bytes</span>
        </div>
      </header>

      <section className="experiment-config toolbar" aria-label="Evaluation setup">
        <label className="select-field wide-field">
          <span>Model under test</span>
          <select value={model} onChange={(event) => setModel(event.target.value)}>
            {data.experiments.models.map((item) => <option key={item}>{item}</option>)}
          </select>
        </label>
        <label className="select-field">
          <span>Dataset</span>
          <select value={dataset} onChange={(event) => setDataset(event.target.value)}>
            {data.experiments.datasets.map((item) => <option key={item}>{item}</option>)}
          </select>
        </label>
        <div className="field-group">
          <span>Output token cap</span>
          <div className="segmented">
            {data.experiments.tokenCaps.map((value) => (
              <button key={value} type="button" aria-pressed={tokenCap === value} onClick={() => setTokenCap(value)}>{formatNumber(value)}</button>
            ))}
          </div>
        </div>
      </section>

      <section className="experiment-layout">
        <div className="prompt-workspace">
          <div className="workspace-heading">
            <div>
              <p className="eyebrow">Model input</p>
              <h2>Equational implication prompt</h2>
            </div>
            <div className="prompt-metrics">
              <span>{formatNumber(bytes)} bytes</span>
              <span>≈ {formatNumber(estimatedTokens)} tokens</span>
            </div>
          </div>
          <textarea
            className="prompt-editor"
            value={prompt}
            onChange={(event) => persistPrompt(event.target.value)}
            spellCheck={false}
            aria-label="Complete prompt and cheatsheet"
          />
          <div className="validation-row" aria-live="polite">
            {bytes <= data.experiments.promptByteLimit
              ? <span className="valid"><CheckCircle2 size={15} /> Size valid</span>
              : <span className="invalid"><ShieldAlert size={15} /> Over budget by {formatNumber(bytes - data.experiments.promptByteLimit)} bytes</span>}
            {missing.length === 0
              ? <span className="valid"><CheckCircle2 size={15} /> Placeholders valid</span>
              : <span className="invalid"><ShieldAlert size={15} /> Missing {missing.join(", ")}</span>}
          </div>
          <details className="prompt-preview">
            <summary>Rendered sample</summary>
            <pre><code>{renderedPrompt}</code></pre>
          </details>
        </div>

        <aside className="experiment-side">
          <section className="side-section">
            <p className="eyebrow">Required output</p>
            <h2>TRUE / FALSE parser</h2>
            <textarea value={verdictText} onChange={(event) => setVerdictText(event.target.value)} aria-label="Model output for verdict parsing" />
            <div className={`parser-result ${parsedVerdict === null ? "unknown" : parsedVerdict ? "true" : "false"}`}>
              <span>Parsed verdict</span>
              <strong>{parsedVerdict === null ? "UNPARSEABLE" : parsedVerdict ? "TRUE" : "FALSE"}</strong>
            </div>
          </section>
          <section className="side-section version-save">
            <p className="eyebrow">Prompt snapshot</p>
            <h2>Save this setup</h2>
            <label><span>Name</span><input value={versionName} onChange={(event) => setVersionName(event.target.value)} /></label>
            <div className="button-row">
              <button type="button" className="button button-primary" onClick={saveVersion}><Save size={16} /> Save</button>
              <button type="button" className="button" onClick={exportVersion}><Download size={16} /> Export</button>
            </div>
          </section>
        </aside>
      </section>

      <section className="dashboard-section run-section">
        <div className="section-heading">
          <div>
            <p className="eyebrow">Model performance</p>
            <h2>Imported evaluation results</h2>
          </div>
          <label className="button file-button">
            <FileUp size={16} aria-hidden="true" /> Import JSONL
            <input type="file" accept=".json,.jsonl,application/json" onChange={(event) => importRuns(event.target.files?.[0])} />
          </label>
        </div>
        {runError && <p className="form-error">{runError}</p>}
        <div className="run-metrics">
          <div><span>Accuracy</span><strong>{metrics.decided ? formatPercent(metrics.correct, metrics.decided) : "—"}</strong><small>{formatNumber(metrics.correct)} / {formatNumber(metrics.decided)}</small></div>
          <div><span>Parse rate</span><strong>{metrics.total ? formatPercent(metrics.parseable, metrics.total) : "—"}</strong><small>{formatNumber(metrics.parseable)} / {formatNumber(metrics.total)}</small></div>
          <div><span>TRUE recall</span><strong>{metrics.trueTotal ? formatPercent(metrics.trueCorrect, metrics.trueTotal) : "—"}</strong><small>{formatNumber(metrics.trueCorrect)} / {formatNumber(metrics.trueTotal)}</small></div>
          <div><span>FALSE recall</span><strong>{metrics.falseTotal ? formatPercent(metrics.falseCorrect, metrics.falseTotal) : "—"}</strong><small>{formatNumber(metrics.falseCorrect)} / {formatNumber(metrics.falseTotal)}</small></div>
          <div><span>Average output</span><strong>{metrics.avgTokens ? formatNumber(metrics.avgTokens) : "—"}</strong><small>tokens</small></div>
        </div>
      </section>

      <section className="dashboard-section">
        <div className="section-heading">
          <div>
            <p className="eyebrow">Saved in this browser</p>
            <h2>Prompt trials</h2>
          </div>
          <span className="section-count">{formatNumber(versions.length)}</span>
        </div>
        {versions.length ? (
          <table className="data-table versions-table">
            <thead><tr><th>Name</th><th>Model</th><th>Dataset</th><th>Bytes</th><th>Created</th><th><span className="sr-only">Actions</span></th></tr></thead>
            <tbody>
              {versions.map((version) => (
                <tr key={version.id}>
                  <td><button className="text-button" type="button" onClick={() => { persistPrompt(version.prompt); setVersionName(version.name); setModel(version.model); setDataset(version.dataset); setTokenCap(version.tokenCap); }}>{version.name}</button></td>
                  <td><code>{version.model.split("/").at(-1)}</code></td>
                  <td>{version.dataset}</td>
                  <td>{formatNumber(new TextEncoder().encode(version.prompt).length)}</td>
                  <td>{new Date(version.createdAt).toLocaleString()}</td>
                  <td><button type="button" className="icon-button" aria-label={`Delete ${version.name}`} data-tooltip="Delete version" onClick={() => removeVersion(version.id)}><Trash2 size={16} /></button></td>
                </tr>
              ))}
            </tbody>
          </table>
        ) : <div className="empty-state">No prompt versions saved in this browser.</div>}
      </section>
    </div>
  );
}
