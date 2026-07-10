export type LeanStatusName =
  | "dependency-clean"
  | "dependency-debt"
  | "local-debt"
  | "missing-declaration";

export interface LeanStatus {
  represented: boolean;
  declarationPresent: boolean;
  dependencyClean: boolean;
  status: LeanStatusName;
  files: number;
  localPlaceholders: number;
  dependencyPlaceholders: number;
  localAxioms: number;
  dependencyAxioms: number;
  sourcePath: string;
}

export interface PropertyNode {
  id: string;
  shortId: string;
  name: string;
  aliases: string[];
  description: string;
  lean: LeanStatus | null;
  registry: { class: string; tier: string; note?: string } | null;
  referenceUrl: string;
}

export interface SpaceNode {
  id: string;
  shortId: string;
  name: string;
  referenceUrl: string;
  lean: LeanStatus | null;
}

export interface FrontierItem {
  source: string;
  target: string;
  closureGain: number;
  sourceAncestors: number;
  targetDescendants: number;
  setTheory: boolean;
}

export interface DirectEdge {
  source: string;
  target: string;
  theorems: string[];
}

export interface DashboardData {
  schemaVersion: number;
  project: {
    id: string;
    name: string;
    domain: string;
    repoUrl: string;
    upstreamUrl: string;
    referenceUrl: string;
  };
  source: {
    commit: string;
    commitShort: string;
    branch: string;
    sourceDate: string;
    generatedAt: string;
    dataSha: string;
  };
  summary: {
    propertyEntries: number;
    propertyImplementations: number;
    propertyTotal: number;
    mappedProperties: number;
    theoremEntries: number;
    theoremTotal: number;
    theoremDeclarations: number;
    dependencyCleanTheorems: number;
    spaceEntries: number;
    spaceTotal: number;
    resolvedPairs: number;
    totalPairs: number;
    openPairs: number;
  };
  trust: {
    properties: Record<LeanStatusName, number>;
    theorems: Record<LeanStatusName, number>;
    spaces: Record<LeanStatusName, number>;
    projectPlaceholders: number;
    projectAxioms: number;
  };
  graph: {
    size: number;
    counts: Record<string, number>;
    outcomesPath: string;
    witnessesPath: string;
    statusCodes: Record<string, string>;
    direct: DirectEdge[];
    witnessCounts: Record<string, number>;
  };
  properties: PropertyNode[];
  spaces: SpaceNode[];
  frontier: FrontierItem[];
  recentActivity: Array<{
    sha: string;
    short: string;
    date: string;
    subject: string;
  }>;
  latestDelta: Record<string, number>;
  experiments: {
    promptByteLimit: number;
    tokenCaps: number[];
    models: string[];
    datasets: string[];
    requiredPlaceholders: string[];
  };
  downloads: Array<{ label: string; path: string; format: string }>;
}

export interface DashboardBundle {
  data: DashboardData;
  outcomes: Uint8Array;
  witnesses: Uint16Array;
}

export type ReviewKind = "spaces" | "properties" | "theorems";

export interface ReviewTrait {
  property: string;
  name: string;
  value: boolean;
  status: "asserted" | "proven" | "derivable";
  via: string | null;
}

export interface ReviewEntry {
  id: string;
  shortId: string;
  name: string;
  aliases: string[];
  description: string;
  author: string;
  sourcePath: string;
  sourceUrl: string;
  referenceUrl: string;
  code: string;
  extraCode: string;
  leanStatus: LeanStatus;
  traits?: ReviewTrait[];
  traitSummary?: Record<string, number>;
}

export interface ReviewPayload {
  schemaVersion: number;
  kind: ReviewKind;
  sourceCommit: string;
  generatedAt: string;
  chunkSize: number;
  chunks: string[];
  entries: ReviewEntrySummary[];
}

export interface ReviewEntrySummary {
  id: string;
  shortId: string;
  name: string;
  aliases: string[];
  author: string;
  sourceUrl: string;
  referenceUrl: string;
  leanStatus: LeanStatus;
  chunk: number;
}

export interface ReviewChunkPayload {
  schemaVersion: number;
  kind: ReviewKind;
  chunk: number;
  sourceCommit: string;
  entries: ReviewEntry[];
}

export interface ImportedRun {
  model?: string;
  problem_id?: string;
  expected_answer?: boolean;
  correct?: boolean;
  reason?: string;
  finish_reason?: string;
  tokens_in?: number;
  tokens_out?: number;
  latency_ms?: number;
  cost?: number;
  response_text?: string;
  verdict?: boolean | null;
}
