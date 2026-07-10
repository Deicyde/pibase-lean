import { useEffect, useMemo, useRef, useState } from "react";
import { GRAPH_STATUS, graphIndex, type GraphStatusCode } from "../lib";
import type { DashboardBundle } from "../types";

const STATUS_CLASS: Record<number, string> = {
  0: "diagonal",
  1: "explicit-true",
  2: "derived-true",
  3: "false",
  4: "independent",
  5: "open",
};

export type MatrixMode = "all" | "open" | "proofs";

interface MatrixSelection {
  sourceIndex: number;
  targetIndex: number;
}

export default function Matrix({
  bundle,
  selectedSource,
  selectedTarget,
  onSelect,
  mode = "all",
  compact = false,
}: {
  bundle: DashboardBundle;
  selectedSource: string;
  selectedTarget: string;
  onSelect: (source: string, target: string) => void;
  mode?: MatrixMode;
  compact?: boolean;
}) {
  const wrapperRef = useRef<HTMLDivElement>(null);
  const canvasRef = useRef<HTMLCanvasElement>(null);
  const [hover, setHover] = useState<MatrixSelection | null>(null);
  const [side, setSide] = useState(520);
  const properties = bundle.data.properties;
  const size = bundle.data.graph.size;
  const sourceIndex = properties.findIndex((item) => item.id === selectedSource);
  const targetIndex = properties.findIndex((item) => item.id === selectedTarget);

  useEffect(() => {
    const wrapper = wrapperRef.current;
    if (!wrapper) return;
    const observer = new ResizeObserver(([entry]) => {
      const max = compact ? 520 : 760;
      setSide(Math.max(280, Math.min(max, Math.floor(entry.contentRect.width))));
    });
    observer.observe(wrapper);
    return () => observer.disconnect();
  }, [compact]);

  useEffect(() => {
    const canvas = canvasRef.current;
    if (!canvas) return;
    const ratio = window.devicePixelRatio || 1;
    canvas.width = Math.floor(side * ratio);
    canvas.height = Math.floor(side * ratio);
    canvas.style.width = "100%";
    canvas.style.height = "auto";
    const context = canvas.getContext("2d");
    if (!context) return;
    context.setTransform(ratio, 0, 0, ratio, 0, 0);
    const styles = getComputedStyle(document.documentElement);
    const colors: Record<number, string> = {
      0: styles.getPropertyValue("--graph-diagonal").trim(),
      1: styles.getPropertyValue("--graph-explicit").trim(),
      2: styles.getPropertyValue("--graph-derived").trim(),
      3: styles.getPropertyValue("--graph-false").trim(),
      4: styles.getPropertyValue("--graph-independent").trim(),
      5: styles.getPropertyValue("--graph-open").trim(),
    };
    const muted = styles.getPropertyValue("--graph-muted").trim();
    const cell = side / size;
    context.fillStyle = styles.getPropertyValue("--surface").trim();
    context.fillRect(0, 0, side, side);
    for (let row = 0; row < size; row += 1) {
      for (let column = 0; column < size; column += 1) {
        const state = bundle.outcomes[graphIndex(size, row, column)];
        const visible = mode === "all"
          || (mode === "open" && (state === 5 || state === 0))
          || (mode === "proofs" && (state === 1 || state === 2 || state === 0));
        context.fillStyle = visible ? colors[state] : muted;
        context.fillRect(column * cell, row * cell, Math.ceil(cell), Math.ceil(cell));
      }
    }
    if (sourceIndex >= 0 && targetIndex >= 0) {
      context.strokeStyle = styles.getPropertyValue("--ink").trim();
      context.lineWidth = 1.5;
      context.strokeRect(targetIndex * cell + 0.5, sourceIndex * cell + 0.5, Math.max(2, cell), Math.max(2, cell));
      context.globalAlpha = 0.35;
      context.beginPath();
      context.moveTo(0, (sourceIndex + 0.5) * cell);
      context.lineTo(side, (sourceIndex + 0.5) * cell);
      context.moveTo((targetIndex + 0.5) * cell, 0);
      context.lineTo((targetIndex + 0.5) * cell, side);
      context.stroke();
      context.globalAlpha = 1;
    }
  }, [bundle, mode, side, size, sourceIndex, targetIndex]);

  const active = hover ?? (sourceIndex >= 0 && targetIndex >= 0 ? { sourceIndex, targetIndex } : null);
  const activeSummary = useMemo(() => {
    if (!active) return null;
    const state = bundle.outcomes[graphIndex(size, active.sourceIndex, active.targetIndex)] as GraphStatusCode;
    return {
      source: properties[active.sourceIndex],
      target: properties[active.targetIndex],
      state,
    };
  }, [active, bundle.outcomes, properties, size]);

  function pointerSelection(event: React.MouseEvent<HTMLCanvasElement>): MatrixSelection {
    const rect = event.currentTarget.getBoundingClientRect();
    return {
      sourceIndex: Math.max(0, Math.min(size - 1, Math.floor(((event.clientY - rect.top) / rect.height) * size))),
      targetIndex: Math.max(0, Math.min(size - 1, Math.floor(((event.clientX - rect.left) / rect.width) * size))),
    };
  }

  return (
    <div className="matrix" ref={wrapperRef}>
      <div className="matrix-axis matrix-axis-y">Hypothesis ↓</div>
      <canvas
        ref={canvasRef}
        className="matrix-canvas"
        onPointerMove={(event) => setHover(pointerSelection(event))}
        onPointerLeave={() => setHover(null)}
        onClick={(event) => {
          const next = pointerSelection(event);
          onSelect(properties[next.sourceIndex].id, properties[next.targetIndex].id);
        }}
        role="img"
        aria-label={`Implication matrix with ${size} properties. Rows are hypotheses and columns are conclusions.`}
      />
      <div className="matrix-axis matrix-axis-x">Conclusion →</div>
      <div className="matrix-readout" aria-live="polite">
        {activeSummary && (
          <>
            <span className={`matrix-swatch graph-${STATUS_CLASS[activeSummary.state]}`} aria-hidden="true" />
            <strong>{activeSummary.source.shortId}</strong>
            <span>⇒</span>
            <strong>{activeSummary.target.shortId}</strong>
            <span>{GRAPH_STATUS[activeSummary.state].label}</span>
          </>
        )}
      </div>
      <div className="matrix-legend" aria-label="Matrix legend">
        {[1, 2, 3, 4, 5].map((code) => (
          <span key={code}>
            <i className={`matrix-swatch graph-${STATUS_CLASS[code]}`} aria-hidden="true" />
            {GRAPH_STATUS[code as GraphStatusCode].label}
          </span>
        ))}
      </div>
    </div>
  );
}
