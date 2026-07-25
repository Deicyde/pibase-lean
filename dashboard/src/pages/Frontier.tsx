import {
  ArrowRight,
  Bookmark,
  CheckCircle2,
  Download,
  Repeat2,
  RotateCcw,
} from "lucide-react";
import { useEffect, useMemo, useState } from "react";
import MathText from "../components/MathText";
import PropertyCombobox from "../components/PropertyCombobox";
import { downloadText, formatNumber, routeTo } from "../lib";
import type { DashboardBundle, FrontierItem, PropertyNode } from "../types";

type SortKey = "gain" | "source" | "target";
type FrontierView = "formalized" | "pibase";
type EvidenceFilter = "all" | "direct" | "derived" | "conditional";

function resolvePropertyId(
  value: string | null,
  propertyMap: ReadonlyMap<string, PropertyNode>,
  shortIdMap: ReadonlyMap<string, string>,
): string {
  const normalized = value?.trim().toUpperCase();
  if (!normalized) return "";
  if (propertyMap.has(normalized)) return normalized;
  return shortIdMap.get(normalized) ?? "";
}

function legacyPair(params: URLSearchParams): [string | null, string | null] {
  const matches = (params.get("q") ?? "").toUpperCase().match(/P\d+/g) ?? [];
  return [matches[0] ?? null, matches[1] ?? null];
}

function evidenceParam(view: FrontierView, value: string | null): EvidenceFilter {
  if (view === "formalized" && (value === "direct" || value === "derived")) return value;
  if (view === "pibase" && value === "conditional") return value;
  return "all";
}

function sortParam(value: string | null): SortKey {
  return value === "source" || value === "target" ? value : "gain";
}

export default function Frontier({ bundle, params }: { bundle: DashboardBundle; params: URLSearchParams }) {
  const { data } = bundle;
  const propertyMap = useMemo(
    () => new Map(data.properties.map((item) => [item.id, item])),
    [data.properties],
  );
  const shortIdMap = useMemo(
    () => new Map(data.properties.map((item) => [item.shortId.toUpperCase(), item.id])),
    [data.properties],
  );
  const initialView: FrontierView = params.get("view") === "pibase" ? "pibase" : "formalized";
  const [legacySource, legacyTarget] = legacyPair(params);
  const [view, setView] = useState<FrontierView>(initialView);
  const [sourceFilter, setSourceFilter] = useState(
    resolvePropertyId(params.get("source") ?? legacySource, propertyMap, shortIdMap),
  );
  const [targetFilter, setTargetFilter] = useState(
    resolvePropertyId(params.get("target") ?? legacyTarget, propertyMap, shortIdMap),
  );
  const [evidenceFilter, setEvidenceFilter] = useState<EvidenceFilter>(
    evidenceParam(initialView, params.get("evidence")),
  );
  const [definitionsReadyOnly, setDefinitionsReadyOnly] = useState(params.get("ready") === "1");
  const [savedOnly, setSavedOnly] = useState(params.get("saved") === "1");
  const [sort, setSort] = useState<SortKey>(sortParam(params.get("sort")));
  const [limit, setLimit] = useState(60);
  const activeFrontier = view === "formalized" ? data.graph.formalized.frontier : data.frontier;
  const storageKey = `pibase-frontier-watch:${data.source.commit}`;
  const [watched, setWatched] = useState<Set<string>>(() => {
    try { return new Set(JSON.parse(localStorage.getItem(storageKey) ?? "[]") as string[]); }
    catch { return new Set(); }
  });
  const paramKey = params.toString();

  useEffect(() => {
    const nextView: FrontierView = params.get("view") === "pibase" ? "pibase" : "formalized";
    const [nextLegacySource, nextLegacyTarget] = legacyPair(params);
    setView(nextView);
    setSourceFilter(resolvePropertyId(params.get("source") ?? nextLegacySource, propertyMap, shortIdMap));
    setTargetFilter(resolvePropertyId(params.get("target") ?? nextLegacyTarget, propertyMap, shortIdMap));
    setEvidenceFilter(evidenceParam(nextView, params.get("evidence")));
    setDefinitionsReadyOnly(params.get("ready") === "1");
    setSavedOnly(params.get("saved") === "1");
    setSort(sortParam(params.get("sort")));
    setLimit(60);
  }, [paramKey, params, propertyMap, shortIdMap]);

  function isDefinitionsReady(item: FrontierItem): boolean {
    return Boolean(
      propertyMap.get(item.source)?.lean?.declarationPresent
      && propertyMap.get(item.target)?.lean?.declarationPresent,
    );
  }

  function replaceFilterUrl(overrides: Partial<{
    view: FrontierView;
    source: string;
    target: string;
    evidence: EvidenceFilter;
    ready: boolean;
    saved: boolean;
    sort: SortKey;
  }> = {}) {
    const next = {
      view,
      source: sourceFilter,
      target: targetFilter,
      evidence: evidenceFilter,
      ready: definitionsReadyOnly,
      saved: savedOnly,
      sort,
      ...overrides,
    };
    window.history.replaceState(null, "", routeTo("frontier", {
      view: next.view === "pibase" ? "pibase" : undefined,
      source: next.source || undefined,
      target: next.target || undefined,
      evidence: next.evidence === "all" ? undefined : next.evidence,
      ready: next.ready ? "1" : undefined,
      saved: next.saved ? "1" : undefined,
      sort: next.sort === "gain" ? undefined : next.sort,
    }));
  }

  const evidenceCounts = useMemo(() => {
    const counts = { all: activeFrontier.length, direct: 0, derived: 0, conditional: 0 };
    activeFrontier.forEach((item) => {
      if (item.pibaseStatus === "direct") counts.direct += 1;
      if (item.pibaseStatus === "derived") counts.derived += 1;
      if (item.conditionalEvidence) counts.conditional += 1;
    });
    return counts;
  }, [activeFrontier]);

  const definitionsReadyCount = useMemo(
    () => activeFrontier.filter((item) => isDefinitionsReady(item)).length,
    [activeFrontier, propertyMap],
  );
  const savedCount = useMemo(
    () => activeFrontier.filter((item) => watched.has(`${item.source}|${item.target}`)).length,
    [activeFrontier, watched],
  );

  const eligible = useMemo(() => activeFrontier.filter((item) => {
    if (view === "formalized" && evidenceFilter !== "all" && item.pibaseStatus !== evidenceFilter) return false;
    if (view === "pibase" && evidenceFilter === "conditional" && !item.conditionalEvidence) return false;
    if (definitionsReadyOnly && !isDefinitionsReady(item)) return false;
    if (savedOnly && !watched.has(`${item.source}|${item.target}`)) return false;
    return true;
  }), [
    activeFrontier,
    definitionsReadyOnly,
    evidenceFilter,
    propertyMap,
    savedOnly,
    view,
    watched,
  ]);

  const sourceCounts = useMemo(() => {
    const counts = new Map<string, number>();
    eligible.forEach((item) => {
      if (targetFilter && item.target !== targetFilter) return;
      counts.set(item.source, (counts.get(item.source) ?? 0) + 1);
    });
    return counts;
  }, [eligible, targetFilter]);

  const targetCounts = useMemo(() => {
    const counts = new Map<string, number>();
    eligible.forEach((item) => {
      if (sourceFilter && item.source !== sourceFilter) return;
      counts.set(item.target, (counts.get(item.target) ?? 0) + 1);
    });
    return counts;
  }, [eligible, sourceFilter]);

  const filtered = useMemo(() => {
    const rows = eligible.filter((item) => (
      (!sourceFilter || item.source === sourceFilter)
      && (!targetFilter || item.target === targetFilter)
    ));
    rows.sort((left, right) => {
      if (sort === "source") return left.source.localeCompare(right.source) || left.target.localeCompare(right.target);
      if (sort === "target") return left.target.localeCompare(right.target) || left.source.localeCompare(right.source);
      return right.closureGain - left.closureGain || left.source.localeCompare(right.source);
    });
    return rows;
  }, [eligible, sort, sourceFilter, targetFilter]);

  function selectView(nextView: FrontierView) {
    setView(nextView);
    setEvidenceFilter("all");
    setLimit(60);
    replaceFilterUrl({ view: nextView, evidence: "all" });
  }

  function selectSource(nextSource: string) {
    setSourceFilter(nextSource);
    setLimit(60);
    replaceFilterUrl({ source: nextSource });
  }

  function selectTarget(nextTarget: string) {
    setTargetFilter(nextTarget);
    setLimit(60);
    replaceFilterUrl({ target: nextTarget });
  }

  function swapFilters() {
    setSourceFilter(targetFilter);
    setTargetFilter(sourceFilter);
    setLimit(60);
    replaceFilterUrl({ source: targetFilter, target: sourceFilter });
  }

  function selectEvidence(nextEvidence: EvidenceFilter) {
    setEvidenceFilter(nextEvidence);
    setLimit(60);
    replaceFilterUrl({ evidence: nextEvidence });
  }

  function toggleDefinitionsReady() {
    const next = !definitionsReadyOnly;
    setDefinitionsReadyOnly(next);
    setLimit(60);
    replaceFilterUrl({ ready: next });
  }

  function toggleSavedOnly() {
    const next = !savedOnly;
    setSavedOnly(next);
    setLimit(60);
    replaceFilterUrl({ saved: next });
  }

  function selectSort(nextSort: SortKey) {
    setSort(nextSort);
    setLimit(60);
    replaceFilterUrl({ sort: nextSort });
  }

  function resetFilters() {
    setSourceFilter("");
    setTargetFilter("");
    setEvidenceFilter("all");
    setDefinitionsReadyOnly(false);
    setSavedOnly(false);
    setSort("gain");
    setLimit(60);
    replaceFilterUrl({
      source: "",
      target: "",
      evidence: "all",
      ready: false,
      saved: false,
      sort: "gain",
    });
  }

  function watch(item: FrontierItem) {
    const key = `${item.source}|${item.target}`;
    const next = new Set(watched);
    if (next.has(key)) next.delete(key); else next.add(key);
    setWatched(next);
    localStorage.setItem(storageKey, JSON.stringify([...next]));
  }

  function exportFrontier(format: "json" | "csv") {
    const basename = view === "formalized" ? "pibase-formalization-frontier" : "pibase-unclassified-frontier";
    if (format === "json") {
      downloadText(`${basename}.json`, JSON.stringify(filtered, null, 2));
      return;
    }
    const rows = ["source,target,closure_gain,source_ancestors,target_descendants,pibase_status,conditional_evidence,axioms"];
    filtered.forEach((item) => rows.push([
      item.source,
      item.target,
      item.closureGain,
      item.sourceAncestors,
      item.targetDescendants,
      item.pibaseStatus ?? "",
      item.conditionalEvidence ?? false,
      (item.axioms ?? []).join("+"),
    ].join(",")));
    downloadText(`${basename}.csv`, rows.join("\n"), "text/csv");
  }

  const first = filtered[0];
  const firstSource = first ? propertyMap.get(first.source)! : null;
  const firstTarget = first ? propertyMap.get(first.target)! : null;
  const firstReady = first ? isDefinitionsReady(first) : false;
  const hasFilters = Boolean(
    sourceFilter
    || targetFilter
    || evidenceFilter !== "all"
    || definitionsReadyOnly
    || savedOnly
    || sort !== "gain",
  );
  const rankLabel = sort === "gain" ? "closure impact" : sort === "source" ? "hypothesis ID" : "conclusion ID";

  return (
    <div className="page frontier-page">
      <header className="page-intro compact-intro">
        <div>
          <p className="eyebrow">{view === "formalized" ? "Lean graph" : "π-Base graph"}</p>
          <h1>{view === "formalized" ? "Formalization frontier" : "Research frontier"}</h1>
          <p className="page-lede">
            {view === "formalized"
              ? "Known π-Base implications not yet reachable from Lean proofs, ranked by formal closure gain."
              : "Unclassified π-Base implications ranked by potential closure gain, assuming they are true."}
          </p>
        </div>
        <div className="frontier-intro-actions">
          <div className="segmented" aria-label="Frontier source">
            {(["formalized", "pibase"] as FrontierView[]).map((option) => (
              <button key={option} type="button" aria-pressed={view === option} onClick={() => selectView(option)}>
                {option === "formalized" ? "Formalization" : "π-Base"}
              </button>
            ))}
          </div>
          <div className="frontier-total">
            <strong>{formatNumber(filtered.length)}</strong>
            <span>of {formatNumber(activeFrontier.length)} pairs</span>
          </div>
        </div>
      </header>

      <section className="frontier-explorer" aria-label="Frontier filters">
        <div className="frontier-explorer-heading">
          <div>
            <p className="eyebrow">Explore candidates</p>
            <h2>Implication filters</h2>
          </div>
          <button
            className="icon-button"
            type="button"
            aria-label="Reset frontier filters"
            data-tooltip="Reset filters"
            disabled={!hasFilters}
            onClick={resetFilters}
          >
            <RotateCcw size={16} aria-hidden="true" />
          </button>
        </div>

        <div className="frontier-pair-query">
          <PropertyCombobox
            id="frontier-source"
            label="Hypothesis"
            value={sourceFilter}
            properties={data.properties}
            optionCounts={sourceCounts}
            placeholder="Any hypothesis"
            clearable
            onChange={selectSource}
          />
          <button
            type="button"
            className="icon-button frontier-swap"
            aria-label="Swap hypothesis and conclusion filters"
            data-tooltip="Swap filters"
            disabled={!sourceFilter && !targetFilter}
            onClick={swapFilters}
          >
            <Repeat2 size={17} aria-hidden="true" />
          </button>
          <PropertyCombobox
            id="frontier-target"
            label="Conclusion"
            value={targetFilter}
            properties={data.properties}
            optionCounts={targetCounts}
            placeholder="Any conclusion"
            clearable
            onChange={selectTarget}
          />
        </div>

        <div className="frontier-filter-groups">
          <div className="field-group frontier-filter-group">
            <span>{view === "formalized" ? "π-Base evidence" : "Evidence"}</span>
            <div className="segmented frontier-evidence-segments">
              <button type="button" aria-pressed={evidenceFilter === "all"} onClick={() => selectEvidence("all")}>
                All <small>{formatNumber(evidenceCounts.all)}</small>
              </button>
              {view === "formalized" ? (
                <>
                  <button type="button" aria-pressed={evidenceFilter === "direct"} onClick={() => selectEvidence("direct")}>
                    Theorems <small>{formatNumber(evidenceCounts.direct)}</small>
                  </button>
                  <button type="button" aria-pressed={evidenceFilter === "derived"} onClick={() => selectEvidence("derived")}>
                    Closure <small>{formatNumber(evidenceCounts.derived)}</small>
                  </button>
                </>
              ) : (
                <button type="button" aria-pressed={evidenceFilter === "conditional"} onClick={() => selectEvidence("conditional")}>
                  Conditional <small>{formatNumber(evidenceCounts.conditional)}</small>
                </button>
              )}
            </div>
          </div>

          <div className="field-group frontier-filter-group">
            <span>Rank by</span>
            <div className="segmented">
              <button type="button" aria-pressed={sort === "gain"} onClick={() => selectSort("gain")}>Impact</button>
              <button type="button" aria-pressed={sort === "source"} onClick={() => selectSort("source")}>Hypothesis</button>
              <button type="button" aria-pressed={sort === "target"} onClick={() => selectSort("target")}>Conclusion</button>
            </div>
          </div>

          <button
            type="button"
            className="frontier-filter-toggle"
            aria-pressed={definitionsReadyOnly}
            onClick={toggleDefinitionsReady}
          >
            <CheckCircle2 size={16} aria-hidden="true" />
            <span>Definitions ready</span>
            <strong>{formatNumber(definitionsReadyCount)}</strong>
          </button>
          <button
            type="button"
            className="frontier-filter-toggle"
            aria-pressed={savedOnly}
            onClick={toggleSavedOnly}
          >
            <Bookmark size={16} aria-hidden="true" />
            <span>Saved</span>
            <strong>{formatNumber(savedCount)}</strong>
          </button>
        </div>
      </section>

      {first && firstSource && firstTarget && (
        <section className="frontier-top-pick" aria-label="Top matching frontier candidate">
          <div className="frontier-top-label">
            <span>{hasFilters ? "Top match" : view === "formalized" ? "Highest-impact target" : "Highest-impact question"}</span>
            <small>Ranked by {rankLabel}</small>
          </div>
          <div className="frontier-top-pair">
            <div>
              <code>{firstSource.shortId}</code>
              <span>{view === "formalized" ? "⇒" : "⇒?"}</span>
              <code>{firstTarget.shortId}</code>
              {view === "formalized" && (
                <span className="table-tag">π-Base {first.pibaseStatus === "direct" ? "theorem" : "closure"}</span>
              )}
            </div>
            <p>
              <MathText text={firstSource.name} inline />
              <ArrowRight size={14} aria-hidden="true" />
              <MathText text={firstTarget.name} inline />
            </p>
          </div>
          <div className="frontier-top-impact">
            <strong>+{formatNumber(first.closureGain)}</strong>
            <span>{view === "formalized" ? "Lean pairs unlocked" : "cells if true"}</span>
            {view === "formalized" && <small>{firstReady ? "Definitions ready" : "Definitions missing"}</small>}
          </div>
          <a className="button button-primary" href={routeTo("overview", {
            source: first.source,
            target: first.target,
            view: view === "pibase" ? "pibase" : undefined,
          })}>
            Inspect candidate <ArrowRight size={16} aria-hidden="true" />
          </a>
        </section>
      )}

      <div className="frontier-results-heading">
        <div>
          <p className="eyebrow">Ranked results</p>
          <h2>{formatNumber(filtered.length)} candidate implications</h2>
        </div>
        <div className="frontier-downloads">
          <button className="icon-button" type="button" aria-label="Download frontier as CSV" data-tooltip="Download CSV" onClick={() => exportFrontier("csv")}><Download size={17} /></button>
          <button className="icon-button" type="button" aria-label="Download frontier as JSON" data-tooltip="Download JSON" onClick={() => exportFrontier("json")}><span className="json-icon">{`{}`}</span></button>
        </div>
      </div>

      <section className="frontier-table-wrap">
        <table className="data-table frontier-table">
          <thead>
            <tr>
              <th scope="col">Implication</th>
              <th scope="col">Hypothesis</th>
              <th scope="col">Conclusion</th>
              <th scope="col">{view === "formalized" ? "Lean closure gain" : "Potential closure gain"}</th>
              <th scope="col"><span className="sr-only">Actions</span></th>
            </tr>
          </thead>
          <tbody>
            {filtered.slice(0, limit).map((item) => {
              const source = propertyMap.get(item.source)!;
              const target = propertyMap.get(item.target)!;
              const key = `${item.source}|${item.target}`;
              const missingDefinitions = [source, target]
                .filter((property) => !property.lean?.declarationPresent)
                .map((property) => property.shortId);
              return (
                <tr key={key} className={watched.has(key) ? "is-watched" : undefined}>
                  <td>
                    <a className="pair-cell" href={routeTo("overview", {
                      source: item.source,
                      target: item.target,
                      view: view === "pibase" ? "pibase" : undefined,
                    })}>
                      <code>{source.shortId}</code><span>{view === "formalized" ? "⇒" : "⇒?"}</span><code>{target.shortId}</code>
                      {view === "formalized" && (
                        <span className="table-tag">π-Base {item.pibaseStatus === "direct" ? "theorem" : "closure"}</span>
                      )}
                      {view === "pibase" && item.conditionalEvidence && (
                        <span className="table-tag">{(item.axioms ?? []).join(" + ")} counterexample</span>
                      )}
                    </a>
                  </td>
                  <td><MathText text={source.name} inline /></td>
                  <td><MathText text={target.name} inline /></td>
                  <td>
                    <strong>{formatNumber(item.closureGain)}</strong>
                    <span className="cell-detail">
                      {view === "formalized"
                        ? "pairs resolved if formalized"
                        : `${formatNumber(item.sourceAncestors)} ancestors · ${formatNumber(item.targetDescendants)} descendants`}
                    </span>
                    {view === "formalized" && (
                      <span className={`cell-detail frontier-readiness${missingDefinitions.length ? " is-blocked" : ""}`}>
                        {missingDefinitions.length
                          ? `Needs ${missingDefinitions.join(" + ")} definition`
                          : "Definitions ready"}
                      </span>
                    )}
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
                    <a className="icon-link" href={routeTo("overview", {
                      source: item.source,
                      target: item.target,
                      view: view === "pibase" ? "pibase" : undefined,
                    })} aria-label={`Inspect ${source.shortId} implies ${target.shortId}`} data-tooltip="Inspect pair"><ArrowRight size={17} /></a>
                  </td>
                </tr>
              );
            })}
          </tbody>
        </table>
        {!filtered.length && (
          <div className="empty-state">
            No {view === "formalized" ? "formalization candidates" : "unclassified pairs"} match these filters.
          </div>
        )}
      </section>

      {limit < filtered.length && (
        <div className="load-more"><button type="button" className="button" onClick={() => setLimit((value) => value + 60)}>Show 60 more</button></div>
      )}
    </div>
  );
}
