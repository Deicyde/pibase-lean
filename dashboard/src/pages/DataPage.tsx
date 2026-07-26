import { Download, ExternalLink, FileCode2 } from "lucide-react";
import type { DashboardData } from "../types";

const DOWNLOAD_DESCRIPTIONS: Record<string, string> = {
  "data/dashboard.json": "Source versions, summary counts, properties, spaces, and graph metadata.",
  "data/outcomes.bin": "Every ordered property pair classified from the pinned π-Base dataset.",
  "data/formalized-outcomes.bin": "Lean-verified implications, including pairs obtained by transitive closure.",
  "data/witnesses.bin": "Indexes the separating spaces used for unconditional counterexamples.",
  "data/axiom-dependencies.json": "Implications known to be independent of ZFC, with the assumptions controlling each truth value.",
  "data/formalization-frontier.json": "π-Base implications ready to prove using existing Lean definitions.",
  "data/frontier.json": "Pairs that remain unresolved in the pinned π-Base dataset.",
  "data/review-spaces.json": "Space records and their Lean implementation status.",
  "data/review-properties.json": "Property definitions and their well-definedness audit.",
  "data/review-theorems.json": "Theorem records, declarations, and placeholder audit.",
};

const IMPLICATION_TERMS = [
  {
    term: "Lean theorem",
    definition: "A direct property implication with a canonical theorem whose own theorem files contain no active placeholder or explicit axiom.",
  },
  {
    term: "By transitive closure",
    definition: "A pair resolved by composing direct Lean proofs. It is not a separate theorem declaration.",
  },
  {
    term: "Not yet formalized",
    definition: "No direct or transitive Lean proof currently resolves the pair.",
  },
  {
    term: "Unconditional counterexample",
    definition: "A separating π-Base space refutes the implication without requiring an additional set-theoretic assumption.",
  },
  {
    term: "Independent of ZFC",
    definition: "The implication is true in some models of ZFC and false in others; a named statement such as CH records which side holds.",
  },
  {
    term: "Unclassified",
    definition: "The pinned π-Base data contains no unconditional proof, unconditional witness, or axiom-dependence certificate.",
  },
];

const AUDIT_TERMS = [
  {
    term: "Property coverage",
    definition: "The canonical Lean definition exists. A separate well-definedness proof may still contain a placeholder; Review flags those cases.",
  },
  {
    term: "Theorem coverage",
    definition: "The π-Base theorem record has a canonical Lean declaration with no active placeholder in its own theorem files.",
  },
  {
    term: "Dependency-clean",
    definition: "The declaration and its project import closure contain no active placeholder or explicit project axiom.",
  },
  {
    term: "Dependency debt",
    definition: "The declaration has no local placeholder, but at least one imported project file does. This does not prove that the declaration uses that debt.",
  },
  {
    term: "Local debt",
    definition: "The entity's own Lean files contain an active sorry or admit.",
  },
  {
    term: "Missing declaration",
    definition: "The expected canonical bundled declaration is absent from the entity's primary file.",
  },
];

export default function DataPage({ data }: { data: DashboardData }) {
  const downloadGroups = [
    {
      key: "manifest",
      title: "Start here",
      summary: "One readable JSON file describing this dashboard build.",
      items: data.downloads.filter((item) => item.path === "data/dashboard.json"),
    },
    {
      key: "graph",
      title: "Graph and frontier data",
      summary: "Machine-readable classifications, witnesses, and open targets.",
      items: data.downloads.filter(
        (item) => item.path !== "data/dashboard.json" && !item.path.startsWith("data/review-"),
      ),
    },
    {
      key: "review",
      title: "Review audit data",
      summary: "Detailed source records used by the Review page.",
      items: data.downloads.filter((item) => item.path.startsWith("data/review-")),
    },
  ];

  return (
    <div className="page data-page">
      <header className="page-intro compact-intro">
        <div>
          <p className="eyebrow">Dashboard provenance</p>
          <h1>Sources &amp; downloads</h1>
          <p className="page-lede">
            See which projects supply the dashboard data and download the generated graph, frontier, and review files.
          </p>
        </div>
        <a className="button" href="blueprint.html"><FileCode2 size={16} /> Technical blueprint</a>
      </header>

      <section className="dashboard-section data-first-section" aria-labelledby="data-sources-heading">
        <div className="section-heading">
          <div>
            <p className="eyebrow">Source projects</p>
            <h2 id="data-sources-heading">Where the data comes from</h2>
            <p className="section-summary">The dashboard combines Felix's Lean formalization with the π-Base reference dataset.</p>
          </div>
        </div>
        <div className="data-source-list">
          <article>
            <span>Lean formalization</span>
            <h3>felixpernegger/pibase-lean</h3>
            <p>Definitions and proofs used for the Lean-verified implication graph.</p>
            <a className="text-link" href={data.project.repoUrl}>
              Open Felix's repository <ExternalLink size={13} aria-hidden="true" />
            </a>
          </article>
          <article>
            <span>Reference dataset</span>
            <h3>π-Base data</h3>
            <p>Properties, theorem records, and spaces used to classify the complete implication graph.</p>
            <a className="text-link" href="https://github.com/pi-base/data">
              Open π-Base data <ExternalLink size={13} aria-hidden="true" />
            </a>
          </article>
        </div>
        <p className="data-source-note">
          <FileCode2 size={14} aria-hidden="true" />
          Exact pinned versions and build metadata remain available in the <a href="data/dashboard.json">dashboard manifest</a>.
        </p>
      </section>

      <section className="dashboard-section" aria-labelledby="downloads-heading">
        <div className="section-heading">
          <div>
            <p className="eyebrow">Reusable files</p>
            <h2 id="downloads-heading">Downloads</h2>
            <p className="section-summary">Files are grouped by purpose; the description explains what each one contains.</p>
          </div>
        </div>
        <div className="download-groups">
          {downloadGroups.map((group) => (
            <section className="download-group" key={group.key} aria-labelledby={`download-${group.key}`}>
              <div className="download-group-heading">
                <h3 id={`download-${group.key}`}>{group.title}</h3>
                <p>{group.summary}</p>
              </div>
              <div className="download-list">
                {group.items.map((item) => (
                  <a key={item.path} href={item.path} download aria-label={`Download ${item.label} as ${item.format}`}>
                    <Download size={17} aria-hidden="true" />
                    <span>
                      <strong>{item.label}</strong>
                      <small>{DOWNLOAD_DESCRIPTIONS[item.path] ?? item.path}</small>
                    </span>
                    <span className="download-meta">
                      <code>{item.format}</code>
                      <small>{item.path}</small>
                    </span>
                  </a>
                ))}
              </div>
            </section>
          ))}
        </div>
      </section>

      <section className="dashboard-section" aria-labelledby="terminology-heading">
        <div className="section-heading">
          <div>
            <p className="eyebrow">Reference</p>
            <h2 id="terminology-heading">Dashboard terminology</h2>
            <p className="section-summary">Open a group only when you need a precise definition.</p>
          </div>
        </div>
        <div className="terminology-disclosures">
          <details>
            <summary>Implication classifications <span>{IMPLICATION_TERMS.length} terms</span></summary>
            <dl>
              {IMPLICATION_TERMS.map((item) => (
                <div key={item.term}><dt>{item.term}</dt><dd>{item.definition}</dd></div>
              ))}
            </dl>
          </details>
          <details>
            <summary>Formalization audit terms <span>{AUDIT_TERMS.length} terms</span></summary>
            <dl>
              {AUDIT_TERMS.map((item) => (
                <div key={item.term}><dt>{item.term}</dt><dd>{item.definition}</dd></div>
              ))}
            </dl>
          </details>
        </div>
      </section>
    </div>
  );
}
