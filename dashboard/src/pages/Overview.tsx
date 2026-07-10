import {
  ArrowRight,
  CheckCircle2,
  CircleDotDashed,
  GitCommitHorizontal,
  ShieldCheck,
} from "lucide-react";
import { useState } from "react";
import Matrix, { type MatrixMode } from "../components/Matrix";
import Metric from "../components/Metric";
import TrustBar from "../components/TrustBar";
import { formatNumber, formatPercent, routeTo } from "../lib";
import type { DashboardBundle } from "../types";

export default function Overview({ bundle }: { bundle: DashboardBundle }) {
  const { data } = bundle;
  const [matrixMode, setMatrixMode] = useState<MatrixMode>("all");
  const lead = data.frontier[0];
  const propertyNames = new Map(data.properties.map((item) => [item.id, item]));
  const resolved = data.summary.resolvedPairs;

  return (
    <div className="page overview-page">
      <header className="page-intro overview-intro">
        <div>
          <p className="eyebrow">Lean 4 · Mathlib · topology</p>
          <h1>pibase-lean</h1>
          <p className="page-lede">
            A Lean-checked research view of topological properties, implication proofs,
            separating spaces, and the remaining formal frontier.
          </p>
        </div>
        <dl className="source-ledger">
          <div><dt>Lean source</dt><dd><a href={`${data.project.repoUrl}/commit/${data.source.commit}`}><code>{data.source.commitShort}</code></a></dd></div>
          <div><dt>pi-Base data</dt><dd><code>{data.source.dataSha.slice(0, 12)}</code></dd></div>
          <div><dt>Source date</dt><dd>{data.source.sourceDate}</dd></div>
        </dl>
      </header>

      <section className="metric-grid" aria-label="Project status">
        <Metric
          label="Dependency-clean theorems"
          value={formatNumber(data.summary.dependencyCleanTheorems)}
          detail={`${formatNumber(data.summary.theoremDeclarations)} canonical declarations`}
          tone="clean"
          icon={<ShieldCheck size={18} aria-hidden="true" />}
        />
        <Metric
          label="Properties represented"
          value={formatPercent(data.summary.propertyEntries, data.summary.propertyTotal)}
          detail={`${formatNumber(data.summary.propertyEntries)} of ${formatNumber(data.summary.propertyTotal)} entries`}
          tone="represented"
          icon={<CheckCircle2 size={18} aria-hidden="true" />}
        />
        <Metric
          label="Graph resolved"
          value={formatPercent(resolved, data.summary.totalPairs, 2)}
          detail={`${formatNumber(resolved)} of ${formatNumber(data.summary.totalPairs)} ordered pairs`}
          tone="graph"
          icon={<CircleDotDashed size={18} aria-hidden="true" />}
        />
        <Metric
          label="Open frontier"
          value={formatNumber(data.summary.openPairs)}
          detail={`${formatPercent(data.summary.openPairs, data.summary.totalPairs)} of the graph`}
          tone="open"
          icon={<ArrowRight size={18} aria-hidden="true" />}
        />
      </section>

      <section className="dashboard-section section-split section-graph">
        <div className="section-heading">
          <div>
            <p className="eyebrow">Implication graph</p>
            <h2>Outcome matrix</h2>
          </div>
          <div className="segmented" aria-label="Matrix display mode">
            {(["all", "open", "proofs"] as MatrixMode[]).map((mode) => (
              <button
                key={mode}
                type="button"
                aria-pressed={matrixMode === mode}
                onClick={() => setMatrixMode(mode)}
              >
                {mode === "all" ? "All" : mode === "open" ? "Open" : "True"}
              </button>
            ))}
          </div>
        </div>
        <div className="graph-layout">
          <Matrix
            bundle={bundle}
            selectedSource={lead.source}
            selectedTarget={lead.target}
            onSelect={(source, target) => { window.location.hash = routeTo("explorer", { source, target }); }}
            mode={matrixMode}
            compact
          />
          <div className="outcome-ledger">
            <h3>Outcome ledger</h3>
            <dl>
              <div><dt><i className="matrix-swatch graph-explicit-true" />Explicit pi-Base edge</dt><dd>{formatNumber(data.graph.counts.explicitTrue)}</dd></div>
              <div><dt><i className="matrix-swatch graph-derived-true" />By graph closure</dt><dd>{formatNumber(data.graph.counts.derivedTrue)}</dd></div>
              <div><dt><i className="matrix-swatch graph-false" />Counterexample</dt><dd>{formatNumber(data.graph.counts.false)}</dd></div>
              <div><dt><i className="matrix-swatch graph-independent" />Independent</dt><dd>{formatNumber(data.graph.counts.independent ?? 0)}</dd></div>
              <div><dt><i className="matrix-swatch graph-open" />Open</dt><dd>{formatNumber(data.graph.counts.open)}</dd></div>
            </dl>
            <a className="text-link" href={routeTo("explorer", { source: lead.source, target: lead.target })}>
              Open graph explorer <ArrowRight size={15} aria-hidden="true" />
            </a>
          </div>
        </div>
      </section>

      <section className="dashboard-section section-split">
        <div className="section-heading">
          <div>
            <p className="eyebrow">Formal trust</p>
            <h2>Lean status ledger</h2>
          </div>
          <a className="text-link" href={routeTo("review")}>Open review <ArrowRight size={15} aria-hidden="true" /></a>
        </div>
        <div className="trust-ledger">
          <TrustBar label="Properties" values={data.trust.properties} />
          <TrustBar label="Theorems" values={data.trust.theorems} />
          <TrustBar label="Spaces" values={data.trust.spaces} />
          <div className="trust-note">
            <strong>{formatNumber(data.trust.projectPlaceholders)}</strong>
            <span>active Lean placeholders</span>
            <strong>{formatNumber(data.trust.projectAxioms)}</strong>
            <span>explicit project axioms</span>
          </div>
        </div>
      </section>

      <section className="dashboard-section two-column-section">
        <div>
          <div className="section-heading">
            <div>
              <p className="eyebrow">Highest leverage</p>
              <h2>Open frontier</h2>
            </div>
            <a className="text-link" href={routeTo("frontier")}>View all <ArrowRight size={15} aria-hidden="true" /></a>
          </div>
          <ol className="frontier-preview">
            {data.frontier.slice(0, 6).map((item) => {
              const source = propertyNames.get(item.source)!;
              const target = propertyNames.get(item.target)!;
              return (
                <li key={`${item.source}-${item.target}`}>
                  <a href={routeTo("explorer", { source: item.source, target: item.target })}>
                    <span className="pair-label"><code>{source.shortId}</code> <span>⇒?</span> <code>{target.shortId}</code></span>
                    <span className="pair-names">{source.name} → {target.name}</span>
                    <span className="gain">+{formatNumber(item.closureGain)} cells</span>
                  </a>
                </li>
              );
            })}
          </ol>
        </div>
        <div>
          <div className="section-heading">
            <div>
              <p className="eyebrow">Repository</p>
              <h2>Recent activity</h2>
            </div>
          </div>
          <ol className="activity-list">
            {data.recentActivity.slice(0, 6).map((commit) => (
              <li key={commit.sha}>
                <GitCommitHorizontal size={16} aria-hidden="true" />
                <div>
                  <a href={`${data.project.repoUrl}/commit/${commit.sha}`}>{commit.subject}</a>
                  <span><code>{commit.short}</code> · {commit.date}</span>
                </div>
              </li>
            ))}
          </ol>
        </div>
      </section>
    </div>
  );
}
