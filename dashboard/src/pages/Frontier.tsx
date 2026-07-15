import { ArrowRight, Bookmark, Download, Search, Sparkles } from "lucide-react";
import { useMemo, useState } from "react";
import MathText from "../components/MathText";
import { downloadText, formatNumber, routeTo } from "../lib";
import type { DashboardBundle, FrontierItem } from "../types";

type SortKey = "gain" | "source" | "target";

export default function Frontier({ bundle, params }: { bundle: DashboardBundle; params: URLSearchParams }) {
  const { data } = bundle;
  const [query, setQuery] = useState(params.get("q") ?? "");
  const [conditionalOnly, setConditionalOnly] = useState(false);
  const [sort, setSort] = useState<SortKey>("gain");
  const [limit, setLimit] = useState(60);
  const propertyMap = useMemo(() => new Map(data.properties.map((item) => [item.id, item])), [data.properties]);
  const storageKey = `pibase-frontier-watch:${data.source.commit}`;
  const [watched, setWatched] = useState<Set<string>>(() => {
    try { return new Set(JSON.parse(localStorage.getItem(storageKey) ?? "[]") as string[]); }
    catch { return new Set(); }
  });

  const filtered = useMemo(() => {
    const term = query.trim().toLowerCase();
    const exactIds = term.split(/\s+/).map((value) => value.toUpperCase());
    const rows = data.frontier.filter((item) => {
      if (conditionalOnly && !item.conditionalEvidence) return false;
      if (!term) return true;
      const source = propertyMap.get(item.source)!;
      const target = propertyMap.get(item.target)!;
      if (exactIds.length === 2 && source.shortId === exactIds[0] && target.shortId === exactIds[1]) return true;
      return [source.shortId, source.name, ...source.aliases, target.shortId, target.name, ...target.aliases]
        .join(" ").toLowerCase().includes(term);
    });
    rows.sort((left, right) => {
      if (sort === "source") return left.source.localeCompare(right.source);
      if (sort === "target") return left.target.localeCompare(right.target);
      return right.closureGain - left.closureGain || left.source.localeCompare(right.source);
    });
    return rows;
  }, [conditionalOnly, data.frontier, propertyMap, query, sort]);

  function watch(item: FrontierItem) {
    const key = `${item.source}|${item.target}`;
    const next = new Set(watched);
    if (next.has(key)) next.delete(key); else next.add(key);
    setWatched(next);
    localStorage.setItem(storageKey, JSON.stringify([...next]));
  }

  function exportFrontier(format: "json" | "csv") {
    if (format === "json") {
      downloadText("pibase-unclassified-frontier.json", JSON.stringify(filtered, null, 2));
      return;
    }
    const rows = ["source,target,closure_gain,source_ancestors,target_descendants,conditional_evidence,axioms"];
    filtered.forEach((item) => rows.push([
      item.source,
      item.target,
      item.closureGain,
      item.sourceAncestors,
      item.targetDescendants,
      item.conditionalEvidence,
      item.axioms.join("+"),
    ].join(",")));
    downloadText("pibase-unclassified-frontier.csv", rows.join("\n"), "text/csv");
  }

  const first = filtered[0];
  return (
    <div className="page frontier-page">
      <header className="page-intro compact-intro">
        <div>
          <p className="eyebrow">Unclassified graph</p>
          <h1>Frontier</h1>
          <p className="page-lede">Potential transitive-closure gain, assuming the implication is true.</p>
        </div>
        <div className="frontier-total"><strong>{formatNumber(filtered.length)}</strong><span>matching pairs</span></div>
      </header>

      <section className="toolbar frontier-toolbar" aria-label="Frontier filters">
        <label className="search-field">
          <span className="sr-only">Search frontier</span>
          <Search size={16} aria-hidden="true" />
          <input value={query} onChange={(event) => { setQuery(event.target.value); setLimit(60); }} placeholder="Property ID or name" />
        </label>
        <label className="select-field">
          <span>Order</span>
          <select value={sort} onChange={(event) => setSort(event.target.value as SortKey)}>
            <option value="gain">Closure gain</option>
            <option value="source">Hypothesis ID</option>
            <option value="target">Conclusion ID</option>
          </select>
        </label>
        <label className="check-field">
          <input type="checkbox" checked={conditionalOnly} onChange={(event) => setConditionalOnly(event.target.checked)} />
          <span>Conditional evidence</span>
        </label>
        {first && (
          <a className="button button-primary" href={routeTo("overview", { source: first.source, target: first.target, view: "pibase" })}>
            <Sparkles size={16} aria-hidden="true" /> Largest potential gain
          </a>
        )}
        <div className="toolbar-spacer" />
        <button className="icon-button" type="button" aria-label="Download frontier as CSV" data-tooltip="Download CSV" onClick={() => exportFrontier("csv")}><Download size={17} /></button>
        <button className="icon-button" type="button" aria-label="Download frontier as JSON" data-tooltip="Download JSON" onClick={() => exportFrontier("json")}><span className="json-icon">{`{}`}</span></button>
      </section>

      <section className="frontier-table-wrap">
        <table className="data-table frontier-table">
          <thead>
            <tr>
              <th scope="col">Implication</th>
              <th scope="col">Hypothesis</th>
              <th scope="col">Conclusion</th>
              <th scope="col">Closure gain</th>
              <th scope="col"><span className="sr-only">Actions</span></th>
            </tr>
          </thead>
          <tbody>
            {filtered.slice(0, limit).map((item) => {
              const source = propertyMap.get(item.source)!;
              const target = propertyMap.get(item.target)!;
              const key = `${item.source}|${item.target}`;
              return (
                <tr key={key} className={watched.has(key) ? "is-watched" : undefined}>
                  <td>
                    <a className="pair-cell" href={routeTo("overview", { source: item.source, target: item.target, view: "pibase" })}>
                      <code>{source.shortId}</code><span>⇒?</span><code>{target.shortId}</code>
                      {item.conditionalEvidence && <span className="table-tag">{item.axioms.join(" + ")} counterexample</span>}
                    </a>
                  </td>
                  <td><MathText text={source.name} inline /></td>
                  <td><MathText text={target.name} inline /></td>
                  <td>
                    <strong>{formatNumber(item.closureGain)}</strong>
                    <span className="cell-detail">{formatNumber(item.sourceAncestors)} ancestors · {formatNumber(item.targetDescendants)} descendants</span>
                  </td>
                  <td className="row-actions">
                    <button
                      type="button"
                      className="icon-button"
                      aria-label={watched.has(key) ? "Remove from saved frontier" : "Save frontier pair"}
                      aria-pressed={watched.has(key)}
                      data-tooltip={watched.has(key) ? "Remove saved pair" : "Save pair"}
                      onClick={() => watch(item)}
                    ><Bookmark size={16} fill={watched.has(key) ? "currentColor" : "none"} /></button>
                    <a className="icon-link" href={routeTo("overview", { source: item.source, target: item.target, view: "pibase" })} aria-label={`Inspect ${source.shortId} implies ${target.shortId}`} data-tooltip="Inspect pair"><ArrowRight size={17} /></a>
                  </td>
                </tr>
              );
            })}
          </tbody>
        </table>
        {!filtered.length && <div className="empty-state">No unclassified pairs match these filters.</div>}
      </section>

      {limit < filtered.length && (
        <div className="load-more"><button type="button" className="button" onClick={() => setLimit((value) => value + 60)}>Show 60 more</button></div>
      )}
    </div>
  );
}
