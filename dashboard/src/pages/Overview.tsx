import {
  ArrowRight,
  CheckCircle2,
  CircleDotDashed,
  ExternalLink,
  GitBranch,
  GitCommitHorizontal,
  Repeat2,
  ShieldCheck,
} from "lucide-react";
import { lazy, Suspense, useEffect, useMemo, useState } from "react";
import ImplementationBar from "../components/ImplementationBar";
import Matrix, { type MatrixMode, type MatrixView } from "../components/Matrix";
import Metric from "../components/Metric";
import TrustBar from "../components/TrustBar";
import {
  FORMAL_GRAPH_STATUS,
  GRAPH_STATUS,
  findProofPath,
  formatNumber,
  formatPercent,
  graphIndex,
  plainMathLabel,
  routeTo,
  type GraphStatusCode,
} from "../lib";
import type { DashboardBundle } from "../types";

const MathText = lazy(() => import("../components/MathText"));

const PIBASE_STATUS_CLASS: Record<number, string> = {
  0: "diagonal",
  1: "explicit-true",
  2: "derived-true",
  3: "false",
  4: "independent",
  5: "open",
};

function statusClass(view: MatrixView, state: GraphStatusCode): string {
  if (view === "formalized") {
    if (state === 1) return "formal-direct";
    if (state === 2) return "formal-derived";
    return state === 0 ? "diagonal" : "unformalized";
  }
  return PIBASE_STATUS_CLASS[state];
}

export default function Overview({ bundle, params }: { bundle: DashboardBundle; params: URLSearchParams }) {
  const { data } = bundle;
  const [matrixMode, setMatrixMode] = useState<MatrixMode>("all");
  const [matrixView, setMatrixView] = useState<MatrixView>(params.get("view") === "pibase" ? "pibase" : "formalized");
  const lead = data.graph.formalized.direct[0]
    ?? data.frontier[0]
    ?? { source: data.properties[0].id, target: data.properties[0].id };
  const validIds = useMemo(() => new Set(data.properties.map((item) => item.id)), [data.properties]);
  const [source, setSource] = useState(validIds.has(params.get("source") ?? "") ? params.get("source")! : lead.source);
  const [target, setTarget] = useState(validIds.has(params.get("target") ?? "") ? params.get("target")! : lead.target);
  const propertyNames = new Map(data.properties.map((item) => [item.id, item]));
  const resolved = data.summary.resolvedPairs;
  const formalDirectCount = data.graph.formalized.counts.formalizedDirect ?? 0;
  const formalDerivedCount = data.graph.formalized.counts.formalizedDerived ?? 0;
  const formalPairCount = formalDirectCount + formalDerivedCount;
  const sourceIndex = data.properties.findIndex((item) => item.id === source);
  const targetIndex = data.properties.findIndex((item) => item.id === target);
  const sourceNode = data.properties[sourceIndex];
  const targetNode = data.properties[targetIndex];
  const activeOutcomes = matrixView === "formalized" ? bundle.formalizedOutcomes : bundle.outcomes;
  const activeDirect = matrixView === "formalized" ? data.graph.formalized.direct : data.graph.direct;
  const state = activeOutcomes[graphIndex(data.graph.size, sourceIndex, targetIndex)] as GraphStatusCode;
  const pibaseState = bundle.outcomes[graphIndex(data.graph.size, sourceIndex, targetIndex)] as GraphStatusCode;
  const statusLabels = matrixView === "formalized" ? FORMAL_GRAPH_STATUS : GRAPH_STATUS;
  const direct = activeDirect.find((edge) => edge.source === source && edge.target === target);
  const path = state === 2 ? findProofPath(data, source, target, activeDirect) : [];
  const proofPath = path.map((id) => propertyNames.get(id)!);
  const witnessValue = bundle.witnesses[graphIndex(data.graph.size, sourceIndex, targetIndex)];
  const witness = witnessValue ? data.spaces[witnessValue - 1] : null;
  const frontier = pibaseState === 5 ? data.frontier.find((item) => item.source === source && item.target === target) : null;
  const paramKey = params.toString();

  useEffect(() => {
    const nextSource = params.get("source");
    const nextTarget = params.get("target");
    setMatrixView(params.get("view") === "pibase" ? "pibase" : "formalized");
    if (!nextSource || !nextTarget || !validIds.has(nextSource) || !validIds.has(nextTarget)) return;
    setSource(nextSource);
    setTarget(nextTarget);
    const frame = window.requestAnimationFrame(() => {
      document.getElementById("implication-explorer")?.scrollIntoView({ block: "start" });
    });
    return () => window.cancelAnimationFrame(frame);
  }, [paramKey, params, validIds]);

  function selectPair(nextSource: string, nextTarget: string) {
    setSource(nextSource);
    setTarget(nextTarget);
    window.history.replaceState(null, "", routeTo("overview", {
      source: nextSource,
      target: nextTarget,
      view: matrixView === "pibase" ? "pibase" : undefined,
    }));
  }

  function selectMatrixView(nextView: MatrixView) {
    setMatrixView(nextView);
    window.history.replaceState(null, "", routeTo("overview", {
      source,
      target,
      view: nextView === "pibase" ? "pibase" : undefined,
    }));
  }

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
          label="Lean implication graph"
          value={formatNumber(formalPairCount)}
          detail={`${formatNumber(formalDirectCount)} direct · ${formatNumber(formalDerivedCount)} by closure`}
          tone="clean"
          icon={<ShieldCheck size={18} aria-hidden="true" />}
        />
        <Metric
          label="Properties implemented"
          value={formatPercent(data.summary.propertyImplementations, data.summary.propertyTotal)}
          detail={`${formatNumber(data.summary.propertyImplementations)} definitions · ${formatNumber(data.summary.propertyTotal - data.summary.propertyImplementations)} remaining`}
          tone="represented"
          icon={<CheckCircle2 size={18} aria-hidden="true" />}
        />
        <Metric
          label="pi-Base classified"
          value={formatPercent(resolved, data.summary.totalPairs, 2)}
          detail={`${formatNumber(resolved)} of ${formatNumber(data.summary.totalPairs)} ordered pairs`}
          tone="graph"
          icon={<CircleDotDashed size={18} aria-hidden="true" />}
        />
        <Metric
          label="pi-Base open pairs"
          value={formatNumber(data.summary.openPairs)}
          detail={`${formatPercent(data.summary.openPairs, data.summary.totalPairs)} of the graph`}
          tone="open"
          icon={<ArrowRight size={18} aria-hidden="true" />}
        />
      </section>

      <section id="implication-explorer" className="dashboard-section section-graph">
        <div className="section-heading">
          <div>
            <p className="eyebrow">Implication graph</p>
            <h2>Explorer</h2>
          </div>
          <div className="explorer-heading-actions">
            <div className="segmented" aria-label="Implication source">
              {(["formalized", "pibase"] as MatrixView[]).map((view) => (
                <button
                  key={view}
                  type="button"
                  aria-pressed={matrixView === view}
                  onClick={() => selectMatrixView(view)}
                >
                  {view === "formalized" ? "Formalized" : "pi-Base"}
                </button>
              ))}
            </div>
            <div className={`outcome-chip graph-${statusClass(matrixView, state)}`}>
              <i className={`matrix-swatch graph-${statusClass(matrixView, state)}`} aria-hidden="true" />
              {statusLabels[state].label}
            </div>
          </div>
        </div>

        <div className="pair-controls" aria-label="Selected implication">
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
        </div>

        <div className="explorer-layout">
          <div className="matrix-workspace">
            <div className="matrix-toolbar">
              <span>
                {matrixView === "formalized"
                  ? `${formatNumber(formalDirectCount)} direct · ${formatNumber(formalDerivedCount)} by closure`
                  : `${formatNumber(data.graph.counts.explicitTrue)} direct · ${formatNumber(data.graph.counts.derivedTrue)} by closure`}
              </span>
              <div className="segmented" aria-label="Matrix display mode">
                {(["all", "open", "proofs"] as MatrixMode[]).map((mode) => (
                  <button
                    key={mode}
                    type="button"
                    aria-pressed={matrixMode === mode}
                    onClick={() => setMatrixMode(mode)}
                  >
                    {mode === "all"
                      ? "All"
                      : mode === "open"
                        ? matrixView === "formalized" ? "Remaining" : "Open"
                        : matrixView === "formalized" ? "Proofs" : "True"}
                  </button>
                ))}
              </div>
            </div>
            <Matrix
              bundle={bundle}
              selectedSource={source}
              selectedTarget={target}
              onSelect={selectPair}
              outcomes={activeOutcomes}
              view={matrixView}
              mode={matrixMode}
            />
          </div>

          <aside className="pair-inspector" aria-label="Pair evidence">
            <div className="inspector-head">
              <p className="eyebrow">Selected pair</p>
              <div className="pair-equation"><code>{sourceNode.shortId}</code><span>⇒</span><code>{targetNode.shortId}</code></div>
            </div>

            <Suspense fallback={<div className="property-summary-loading" aria-hidden="true" />}>
              <div className="property-summary">
                <div>
                  <span>Hypothesis</span>
                  <h2><MathText text={sourceNode.name} inline /></h2>
                  <MathText text={sourceNode.description} />
                  <a href={sourceNode.referenceUrl}>pi-Base <ExternalLink size={13} aria-hidden="true" /></a>
                </div>
                <div>
                  <span>Conclusion</span>
                  <h2><MathText text={targetNode.name} inline /></h2>
                  <MathText text={targetNode.description} />
                  <a href={targetNode.referenceUrl}>pi-Base <ExternalLink size={13} aria-hidden="true" /></a>
                </div>
              </div>
            </Suspense>

            <div className="evidence-block">
              <h3>Evidence</h3>
              {matrixView === "formalized" ? (
                <>
                  {state === 0 && <p>The hypothesis and conclusion are the same property.</p>}
                  {state === 1 && (
                    <div>
                      <p>Recorded by a canonical Lean theorem declaration for this ordered pair.</p>
                      <div className="evidence-links">
                        {(direct?.theorems ?? []).map((id) => (
                          <a key={id} href={routeTo("review", { kind: "theorems", q: id.replace(/^T0+/, "T") })}><code>{id.replace(/^T0+/, "T")}</code></a>
                        ))}
                      </div>
                    </div>
                  )}
                  {state === 2 && (
                    <div>
                      <p>Derived from {Math.max(0, proofPath.length - 1)} formalized pairwise theorem edges.</p>
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
                  {state === 5 && (
                    <div>
                      <p>No canonical pairwise Lean theorem path is currently recorded for this implication.</p>
                      <dl className="frontier-evidence">
                        <div><dt>pi-Base classification</dt><dd>{GRAPH_STATUS[pibaseState].label}</dd></div>
                      </dl>
                    </div>
                  )}
                </>
              ) : (
                <>
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
                      <p>Derived from {Math.max(0, proofPath.length - 1)} explicit pi-Base theorem edges.</p>
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
                </>
              )}
            </div>

            <div className="inspector-actions">
              <a href={routeTo("review", { kind: "properties", q: sourceNode.shortId })}><GitBranch size={15} aria-hidden="true" /> Review {sourceNode.shortId}</a>
              <a href={routeTo("review", { kind: "properties", q: targetNode.shortId })}><GitBranch size={15} aria-hidden="true" /> Review {targetNode.shortId}</a>
            </div>
          </aside>
        </div>
      </section>

      <section className="dashboard-section section-split">
        <div className="section-heading">
          <div>
            <p className="eyebrow">Formalization status</p>
            <h2>Lean implementation ledger</h2>
          </div>
          <a className="text-link" href={routeTo("review")}>Open review <ArrowRight size={15} aria-hidden="true" /></a>
        </div>
        <div className="trust-ledger">
          <ImplementationBar
            label="Properties"
            implemented={data.summary.propertyImplementations}
            total={data.summary.propertyTotal}
          />
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
                  <a href={routeTo("overview", { source: item.source, target: item.target })}>
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
