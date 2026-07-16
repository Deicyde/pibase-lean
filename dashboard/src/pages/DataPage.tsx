import { Download, ExternalLink, FileCode2, GitCommitHorizontal } from "lucide-react";
import TrustBar from "../components/TrustBar";
import { formatNumber, formatPercent, plainMathLabel, routeTo } from "../lib";
import type { DashboardData } from "../types";

export default function DataPage({ data }: { data: DashboardData }) {
  const propertyMap = new Map(data.properties.map((item) => [item.id, item]));
  const conditionalSpaces = data.spaces.filter((item) => item.assumptions.length);

  return (
    <div className="page data-page">
      <header className="page-intro compact-intro">
        <div>
          <p className="eyebrow">Reproducibility</p>
          <h1>Data ledger</h1>
          <p className="page-lede">Versioned formalization, graph, evidence, and review artifacts.</p>
        </div>
        <a className="button" href="blueprint.html"><FileCode2 size={16} /> Blueprint</a>
      </header>

      <section className="source-grid" aria-label="Source versions">
        <article>
          <span>Lean source</span>
          <strong><code>{data.source.commitShort}</code></strong>
          <p>{data.project.repositoryLabel} · {data.source.sourceDate}</p>
          <a href={`${data.project.repoUrl}/commit/${data.source.commit}`}>Commit <ExternalLink size={13} /></a>
        </article>
        <article>
          <span>pi-Base snapshot</span>
          <strong><code>{data.source.dataSha.slice(0, 12)}</code></strong>
          <p>{formatNumber(data.summary.propertyTotal)} properties · {formatNumber(data.summary.theoremTotal)} theorem records</p>
          <a href={`https://github.com/pi-base/data/tree/${data.source.dataSha}`}>Snapshot <ExternalLink size={13} /></a>
        </article>
        <article>
          <span>Dashboard schema</span>
          <strong>Version {data.schemaVersion}</strong>
          <p>Generated {new Date(data.source.generatedAt).toLocaleString()}</p>
          <a href="data/dashboard.json">Manifest <ExternalLink size={13} /></a>
        </article>
      </section>

      <section className="dashboard-section">
        <div className="section-heading">
          <div>
            <p className="eyebrow">Foundational status</p>
            <h2>Axiom dependencies</h2>
          </div>
          <span className="frontier-total"><strong>{formatNumber(data.graph.axiomDependencies.length)}</strong><span>certified pairs</span></span>
        </div>
        <div className="foundations-grid">
          <div>
            <h3>Implications</h3>
            <table className="data-table foundations-table">
              <thead><tr><th scope="col">Implication</th><th scope="col">Depends on</th><th scope="col">Truth conditions</th><th scope="col">Evidence</th></tr></thead>
              <tbody>
                {data.graph.axiomDependencies.map((item) => {
                  const source = propertyMap.get(item.source)!;
                  const target = propertyMap.get(item.target)!;
                  return (
                    <tr key={`${item.source}-${item.target}`}>
                      <td>
                        <a className="pair-cell" href={routeTo("overview", { source: item.source, target: item.target, view: "pibase" })}>
                          <span><code>{source.shortId}</code> ⇒ <code>{target.shortId}</code></span>
                          <small>{plainMathLabel(source.name)} → {plainMathLabel(target.name)}</small>
                        </a>
                      </td>
                      <td><strong>{item.axioms.join(" + ")}</strong><span className="cell-detail">over {item.baseTheory}</span></td>
                      <td><span>{item.trueWhen}: true</span><span className="cell-detail">{item.falseWhen}: false</span></td>
                      <td><a className="text-link" href={item.referenceUrl}>{item.theorems.map((id) => id.replace(/^T0+/, "T")).join(", ")} <ExternalLink size={13} /></a></td>
                    </tr>
                  );
                })}
              </tbody>
            </table>
          </div>
          <div>
            <h3>Conditional constructions</h3>
            <table className="data-table foundations-table">
              <thead><tr><th scope="col">Space</th><th scope="col">Available under</th></tr></thead>
              <tbody>
                {conditionalSpaces.map((space) => (
                  <tr key={space.id}>
                    <td><a className="pair-cell" href={space.referenceUrl}><code>{space.shortId}</code><small>{plainMathLabel(space.name)}</small></a></td>
                    <td><strong>{space.assumptions.join(" + ")}</strong><span className="cell-detail">Conditional evidence only</span></td>
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
        </div>
      </section>

      <section className="dashboard-section">
        <div className="section-heading">
          <div>
            <p className="eyebrow">π-Base dataset</p>
            <h2>Formalization coverage</h2>
            <p className="section-summary">Lean formalizations compared with every record in the pinned π-Base dataset.</p>
          </div>
        </div>
        <div className="coverage-grid">
          <div className="coverage-item">
            <div><strong>π-Base properties formalized</strong><span>{formatNumber(data.summary.propertyImplementations)} / {formatNumber(data.summary.propertyTotal)}</span></div>
            <div className="coverage-track"><i style={{ width: formatPercent(data.summary.propertyImplementations, data.summary.propertyTotal) }} /></div>
          </div>
          <div className="coverage-item coverage-theorems">
            <div><strong>π-Base theorem records formalized</strong><span>{formatNumber(data.summary.theoremImplementations)} / {formatNumber(data.summary.theoremTotal)}</span></div>
            <div className="coverage-track"><i style={{ width: formatPercent(data.summary.theoremImplementations, data.summary.theoremTotal) }} /></div>
          </div>
          <div className="coverage-item coverage-spaces">
            <div><strong>π-Base spaces formalized</strong><span>{formatNumber(data.summary.spaceImplementations)} / {formatNumber(data.summary.spaceTotal)}</span></div>
            <div className="coverage-track"><i style={{ width: formatPercent(data.summary.spaceImplementations, data.summary.spaceTotal) }} /></div>
          </div>
        </div>
        <div className="trust-ledger data-trust-ledger">
          <div className="data-audit-heading">
            <h3>Dependency audit</h3>
            <p>Trust states classify only the Lean source entries found in Felix's checkout.</p>
          </div>
          <TrustBar label="Property source entries" values={data.trust.properties} />
          <TrustBar label="Theorem source entries" values={data.trust.theorems} />
          {data.summary.spaceEntries > 0 && <TrustBar label="Space source entries" values={data.trust.spaces} />}
        </div>
      </section>

      <section className="dashboard-section">
        <div className="section-heading">
          <div><p className="eyebrow">Artifacts</p><h2>Downloads</h2></div>
        </div>
        <div className="download-list">
          {data.downloads.map((item) => (
            <a key={item.path} href={item.path} download>
              <Download size={17} aria-hidden="true" />
              <span><strong>{item.label}</strong><small>{item.path}</small></span>
              <code>{item.format}</code>
            </a>
          ))}
        </div>
      </section>

      <section className="dashboard-section two-column-section">
        <div>
          <div className="section-heading"><div><p className="eyebrow">Contract</p><h2>Status semantics</h2></div></div>
          <table className="data-table schema-table">
            <tbody>
              <tr><th scope="row">Implemented property or space</th><td>The canonical bundled definition exists. A property still counts when only its separate well-definedness obligation contains a placeholder; Review flags those cases.</td></tr>
              <tr><th scope="row">Formalized theorem record</th><td>The π-Base theorem record has a canonical Lean declaration whose own theorem files contain no active <code>sorry</code>, <code>admit</code>, or explicit axiom.</td></tr>
              <tr><th scope="row">Formalized graph edge</th><td>A positive property-to-property implication with a canonical Lean theorem and no placeholder or explicit axiom in its own theorem files. Conservative import-closure debt is reported separately.</td></tr>
              <tr><th scope="row">Transitive closure cell</th><td>An implication obtained by composing formalized graph edges. It is a resolved pair, not an additional Lean theorem declaration.</td></tr>
              <tr><th scope="row">Formalization frontier</th><td>An implication recorded as true by π-Base but not yet reachable through placeholder-free Lean proofs. Its gain is computed against the Lean implication graph.</td></tr>
              <tr><th scope="row">π-Base frontier</th><td>An implication with no recorded unconditional proof, unconditional separating space, or axiom-dependence certificate in the pinned π-Base dataset. Its gain is hypothetical.</td></tr>
              <tr><th scope="row">Unconditional counterexample</th><td>A separating π-Base space requiring no additional set-theoretic assumption satisfies the hypothesis and refutes the conclusion.</td></tr>
              <tr><th scope="row">Axiom-dependent</th><td>A certificate records that the implication's truth value changes under named assumptions such as CH or MA. The pair is neither unconditionally true nor unconditionally false over the stated base theory.</td></tr>
              <tr><th scope="row">Conditional evidence</th><td>A theorem or separating space is available under an additional assumption. This evidence is displayed, but it does not classify the unconditional implication by itself.</td></tr>
              <tr><th scope="row">Unclassified</th><td>No unconditional theorem path, unconditional witness, or axiom-dependence certificate is currently recorded.</td></tr>
              <tr><th scope="row">Dependency-clean</th><td>Canonical declaration, no local placeholders or explicit axioms, and none in the project import closure.</td></tr>
              <tr><th scope="row">Dependency debt</th><td>Canonical declaration with no local placeholder, but at least one imported project file contains proof debt. This conservative file-level audit does not mean the declaration uses that debt.</td></tr>
              <tr><th scope="row">Local debt</th><td>The entity's own Lean files contain an active <code>sorry</code> or <code>admit</code>.</td></tr>
              <tr><th scope="row">Missing declaration</th><td>The expected canonical bundled declaration is absent from the entity's primary file.</td></tr>
            </tbody>
          </table>
        </div>
        <div>
          <div className="section-heading"><div><p className="eyebrow">Build</p><h2>Pipeline</h2></div></div>
          <ol className="pipeline-list">
            <li><GitCommitHorizontal size={16} /><span><strong>Lean checkout</strong><small>Repository tree and import closure</small></span></li>
            <li><span className="pipeline-index">2</span><span><strong>pi-Base snapshot</strong><small>Properties, theorem rules, spaces, and traits</small></span></li>
            <li><span className="pipeline-index">3</span><span><strong>Graph classification</strong><small>True, false, axiom-dependent, and unclassified</small></span></li>
            <li><span className="pipeline-index">4</span><span><strong>Static application</strong><small>Versioned JSON and packed matrix artifacts</small></span></li>
          </ol>
        </div>
      </section>
    </div>
  );
}
