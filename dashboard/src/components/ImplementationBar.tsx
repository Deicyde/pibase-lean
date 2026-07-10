import { formatNumber, formatPercent } from "../lib";

export default function ImplementationBar({
  label,
  implemented,
  total,
}: {
  label: string;
  implemented: number;
  total: number;
}) {
  const remaining = Math.max(total - implemented, 0);

  return (
    <div className="trust-row">
      <div className="trust-heading">
        <strong>{label}</strong>
        <span>{formatNumber(total)} entries</span>
      </div>
      <div className="trust-track" aria-label={`${label} implementation coverage`}>
        <span
          className="trust-segment implementation-complete"
          style={{ width: `${(implemented / total) * 100}%` }}
          aria-label={`Implemented: ${implemented}`}
        />
        {remaining > 0 && (
          <span
            className="trust-segment implementation-open"
            style={{ width: `${(remaining / total) * 100}%` }}
            aria-label={`Not yet implemented: ${remaining}`}
          />
        )}
      </div>
      <div className="trust-legend">
        <span>
          <i className="legend-dot implementation-complete" aria-hidden="true" />
          Implemented {formatNumber(implemented)} ({formatPercent(implemented, total, 0)})
        </span>
        <span>
          <i className="legend-dot implementation-open" aria-hidden="true" />
          Not yet implemented {formatNumber(remaining)} ({formatPercent(remaining, total, 0)})
        </span>
      </div>
    </div>
  );
}
