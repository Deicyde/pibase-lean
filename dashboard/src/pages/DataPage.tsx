import { Download, ExternalLink, FileCode2, GitCommitHorizontal } from "lucide-react";
import TrustBar from "../components/TrustBar";
import { formatNumber, formatPercent } from "../lib";
import type { DashboardData } from "../types";

export default function DataPage({ data }: { data: DashboardData }) {
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
          <p>{data.source.branch} · {data.source.sourceDate}</p>
          <a href={`${data.project.repoUrl}/commit/${data.source.commit}`}>Commit <ExternalLink size={13} /></a>
        </article>
        <article>
          <span>pi-Base snapshot</span>
          <strong><code>{data.source.dataSha.slice(0, 12)}</code></strong>
          <p>{formatNumber(data.summary.propertyTotal)} properties · {formatNumber(data.summary.theoremTotal)} theorem rows</p>
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
          <div><p className="eyebrow">Coverage</p><h2>Representation and trust</h2></div>
        </div>
        <div className="coverage-grid">
          <div className="coverage-item">
            <div><strong>Properties represented</strong><span>{formatNumber(data.summary.propertyEntries)} / {formatNumber(data.summary.propertyTotal)}</span></div>
            <div className="coverage-track"><i style={{ width: formatPercent(data.summary.propertyEntries, data.summary.propertyTotal) }} /></div>
          </div>
          <div className="coverage-item coverage-theorems">
            <div><strong>Theorem rows represented</strong><span>{formatNumber(data.summary.theoremEntries)} / {formatNumber(data.summary.theoremTotal)}</span></div>
            <div className="coverage-track"><i style={{ width: formatPercent(data.summary.theoremEntries, data.summary.theoremTotal) }} /></div>
          </div>
          <div className="coverage-item coverage-graph">
            <div><strong>Graph resolved</strong><span>{formatNumber(data.summary.resolvedPairs)} / {formatNumber(data.summary.totalPairs)}</span></div>
            <div className="coverage-track"><i style={{ width: formatPercent(data.summary.resolvedPairs, data.summary.totalPairs) }} /></div>
          </div>
        </div>
        <div className="trust-ledger data-trust-ledger">
          <TrustBar label="Properties" values={data.trust.properties} />
          <TrustBar label="Theorems" values={data.trust.theorems} />
          <TrustBar label="Spaces" values={data.trust.spaces} />
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
              <tr><th scope="row">Dependency-clean</th><td>Canonical declaration, no local placeholders or explicit axioms, and none in the project import closure.</td></tr>
              <tr><th scope="row">Dependency debt</th><td>Canonical declaration with no local placeholder, but at least one imported project declaration still contains proof debt.</td></tr>
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
            <li><span className="pipeline-index">3</span><span><strong>Graph classification</strong><small>Explicit, derived, refuted, independent, and open</small></span></li>
            <li><span className="pipeline-index">4</span><span><strong>Static application</strong><small>Versioned JSON and packed matrix artifacts</small></span></li>
          </ol>
        </div>
      </section>
    </div>
  );
}
