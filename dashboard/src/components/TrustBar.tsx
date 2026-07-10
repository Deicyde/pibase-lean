import type { LeanStatusName } from "../types";
import { formatNumber, formatPercent } from "../lib";

const ORDER: LeanStatusName[] = [
  "dependency-clean",
  "dependency-debt",
  "local-debt",
  "missing-declaration",
];

const LABELS: Record<LeanStatusName, string> = {
  "dependency-clean": "Dependency-clean",
  "dependency-debt": "Dependency debt",
  "local-debt": "Local debt",
  "missing-declaration": "Missing declaration",
};

export default function TrustBar({ values, label }: { values: Partial<Record<LeanStatusName, number>>; label: string }) {
  const total = Object.values(values).reduce((sum, value) => sum + (value ?? 0), 0);
  return (
    <div className="trust-row">
      <div className="trust-heading">
        <strong>{label}</strong>
        <span>{formatNumber(total)} entries</span>
      </div>
      <div className="trust-track" aria-label={`${label} trust distribution`}>
        {ORDER.map((key) => {
          const value = values[key] ?? 0;
          if (!value) return null;
          return (
            <span
              key={key}
              className={`trust-segment status-${key}`}
              style={{ width: `${(value / total) * 100}%` }}
              aria-label={`${LABELS[key]}: ${value}`}
            />
          );
        })}
      </div>
      <div className="trust-legend">
        {ORDER.map((key) => {
          const value = values[key] ?? 0;
          if (!value) return null;
          return (
            <span key={key}>
              <i className={`legend-dot status-${key}`} aria-hidden="true" />
              {LABELS[key]} {formatNumber(value)} ({formatPercent(value, total, 0)})
            </span>
          );
        })}
      </div>
    </div>
  );
}
