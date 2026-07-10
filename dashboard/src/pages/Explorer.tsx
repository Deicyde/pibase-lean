import { ArrowRight, ExternalLink, GitBranch, Repeat2 } from "lucide-react";
import { useMemo, useState } from "react";
import MathText from "../components/MathText";
import Matrix, { type MatrixMode } from "../components/Matrix";
import { GRAPH_STATUS, findProofPath, formatNumber, graphIndex, plainMathLabel, routeTo, type GraphStatusCode } from "../lib";
import type { DashboardBundle } from "../types";

const STATUS_CLASS: Record<number, string> = {
  0: "diagonal",
  1: "explicit-true",
  2: "derived-true",
  3: "false",
  4: "independent",
  5: "open",
};

export default function Explorer({ bundle, params }: { bundle: DashboardBundle; params: URLSearchParams }) {
  const { data } = bundle;
  const initial = data.frontier[0];
  const validIds = new Set(data.properties.map((item) => item.id));
  const [source, setSource] = useState(validIds.has(params.get("source") ?? "") ? params.get("source")! : initial.source);
  const [target, setTarget] = useState(validIds.has(params.get("target") ?? "") ? params.get("target")! : initial.target);
  const [mode, setMode] = useState<MatrixMode>("all");
  const sourceIndex = data.properties.findIndex((item) => item.id === source);
  const targetIndex = data.properties.findIndex((item) => item.id === target);
  const sourceNode = data.properties[sourceIndex];
  const targetNode = data.properties[targetIndex];
  const state = bundle.outcomes[graphIndex(data.graph.size, sourceIndex, targetIndex)] as GraphStatusCode;
  const direct = data.graph.direct.find((edge) => edge.source === source && edge.target === target);
  const path = state === 2 ? findProofPath(data, source, target) : [];
  const witnessValue = bundle.witnesses[graphIndex(data.graph.size, sourceIndex, targetIndex)];
  const witness = witnessValue ? data.spaces[witnessValue - 1] : null;
  const frontier = state === 5 ? data.frontier.find((item) => item.source === source && item.target === target) : null;

  const proofPath = useMemo(() => path.map((id) => data.properties.find((item) => item.id === id)!), [data.properties, path]);

  function selectPair(nextSource: string, nextTarget: string) {
    setSource(nextSource);
    setTarget(nextTarget);
    window.history.replaceState(null, "", routeTo("explorer", { source: nextSource, target: nextTarget }));
  }

  return (
    <div className="page explorer-page">
      <header className="page-intro compact-intro">
        <div>
          <p className="eyebrow">Implication graph</p>
          <h1>Explorer</h1>
          <p className="page-lede">Inspect formal evidence for any ordered property pair.</p>
        </div>
        <div className={`outcome-chip graph-${STATUS_CLASS[state]}`}>
          <i className={`matrix-swatch graph-${STATUS_CLASS[state]}`} aria-hidden="true" />
          {GRAPH_STATUS[state].label}
        </div>
      </header>

      <section className="pair-controls" aria-label="Selected implication">
        <label htmlFor="source-property">
          <span>Hypothesis</span>
          <select id="source-property" data-testid="source-property" value={source} onChange={(event) => selectPair(event.target.value, target)}>
            {data.properties.map((item) => <option key={item.id} value={item.id}>{item.shortId} · {plainMathLabel(item.name)}</option>)}
          </select>
        </label>
        <button
          type="button"
          className="icon-button swap-button"
          aria-label="Swap hypothesis and conclusion"
          data-tooltip="Swap direction"
          onClick={() => selectPair(target, source)}
        >
          <Repeat2 size={18} aria-hidden="true" />
        </button>
        <label htmlFor="target-property">
          <span>Conclusion</span>
          <select id="target-property" data-testid="target-property" value={target} onChange={(event) => selectPair(source, event.target.value)}>
            {data.properties.map((item) => <option key={item.id} value={item.id}>{item.shortId} · {plainMathLabel(item.name)}</option>)}
          </select>
        </label>
      </section>

      <section className="explorer-layout">
        <div className="matrix-workspace">
          <div className="matrix-toolbar">
            <span>{formatNumber(data.graph.size)} × {formatNumber(data.graph.size)}</span>
            <div className="segmented" aria-label="Matrix display mode">
              {(["all", "open", "proofs"] as MatrixMode[]).map((item) => (
                <button key={item} type="button" aria-pressed={mode === item} onClick={() => setMode(item)}>
                  {item === "all" ? "All" : item === "open" ? "Open" : "True"}
                </button>
              ))}
            </div>
          </div>
          <Matrix bundle={bundle} selectedSource={source} selectedTarget={target} onSelect={selectPair} mode={mode} />
        </div>

        <aside className="pair-inspector" aria-label="Pair evidence">
          <div className="inspector-head">
            <p className="eyebrow">Selected pair</p>
            <div className="pair-equation"><code>{sourceNode.shortId}</code><span>⇒</span><code>{targetNode.shortId}</code></div>
          </div>

          <div className="property-summary">
            <div>
              <span>Hypothesis</span>
              <h2>{sourceNode.name}</h2>
              <MathText text={sourceNode.description} />
              <a href={sourceNode.referenceUrl}>pi-Base <ExternalLink size={13} aria-hidden="true" /></a>
            </div>
            <div>
              <span>Conclusion</span>
              <h2>{targetNode.name}</h2>
              <MathText text={targetNode.description} />
              <a href={targetNode.referenceUrl}>pi-Base <ExternalLink size={13} aria-hidden="true" /></a>
            </div>
          </div>

          <div className="evidence-block">
            <h3>Evidence</h3>
            {state === 0 && <p>The hypothesis and conclusion are the same property.</p>}
            {state === 1 && (
              <div>
                <p>Recorded as a direct pi-Base theorem edge.</p>
                <div className="evidence-links">
                  {(direct?.theorems ?? []).map((id) => (
                    <a key={id} href={`${data.project.referenceUrl}/theorems/${id}`}><code>{id.replace(/^T0+/, "T")}</code></a>
                  ))}
                </div>
              </div>
            )}
            {state === 2 && (
              <div>
                <p>Derived from {Math.max(0, proofPath.length - 1)} explicit theorem edges.</p>
                <ol className="proof-path">
                  {proofPath.map((node, index) => (
                    <li key={node.id}>
                      <code>{node.shortId}</code><span>{node.name}</span>
                      {index < proofPath.length - 1 && <ArrowRight size={14} aria-hidden="true" />}
                    </li>
                  ))}
                </ol>
              </div>
            )}
            {state === 3 && witness && (
              <div className="witness-evidence">
                <p>A separating space satisfies the hypothesis and refutes the conclusion.</p>
                <a href={witness.referenceUrl}><code>{witness.shortId}</code><strong>{witness.name}</strong><ExternalLink size={14} aria-hidden="true" /></a>
              </div>
            )}
            {state === 4 && <p>An independence certificate is recorded for this ordered pair.</p>}
            {state === 5 && frontier && (
              <div>
                <p>No theorem path, separating space, or independence certificate is currently recorded.</p>
                <dl className="frontier-evidence">
                  <div><dt>Potential closure gain</dt><dd>{formatNumber(frontier.closureGain)}</dd></div>
                  <div><dt>Known ancestors</dt><dd>{formatNumber(frontier.sourceAncestors)}</dd></div>
                  <div><dt>Known descendants</dt><dd>{formatNumber(frontier.targetDescendants)}</dd></div>
                </dl>
                <a className="text-link" href={routeTo("frontier", { q: `${sourceNode.shortId} ${targetNode.shortId}` })}>
                  Open in frontier <ArrowRight size={15} aria-hidden="true" />
                </a>
              </div>
            )}
          </div>

          <div className="inspector-actions">
            <a href={routeTo("review", { kind: "properties", q: sourceNode.shortId })}><GitBranch size={15} aria-hidden="true" /> Review {sourceNode.shortId}</a>
            <a href={routeTo("review", { kind: "properties", q: targetNode.shortId })}><GitBranch size={15} aria-hidden="true" /> Review {targetNode.shortId}</a>
          </div>
        </aside>
      </section>
    </div>
  );
}
