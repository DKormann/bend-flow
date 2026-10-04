import type { TextOverlay } from "./analyzer.js";

export type CheckDiagnostic = {
  uri: string;
  start: number;
  end: number;
  message: string;
  code: "parsing" | "imports" | "checking" | "holes";
};

export type CheckRequest = {
  id: number;
  uri: string;
  path: string;
  version: number;
  overlays: Array<TextOverlay & { version: number }>;
};

export type TypedHover = { uri: string; start: number; end: number; value: string };

export type ValuePreview = { uri: string; offset: number; value: string };

export type CheckResult = {
  id: number;
  uri: string;
  version: number;
  versions: Record<string, number>;
  diagnostics: CheckDiagnostic[];
  hovers: Record<string, string>;
  typedHovers: TypedHover[];
  valuePreviews: ValuePreview[];
};
