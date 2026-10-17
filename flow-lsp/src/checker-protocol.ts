export type FlowCheckOverlay = { path: string; uri: string; text: string; version: number };
export type FlowCheckRequest = { id: number; uri: string; path: string; text: string; version: number; overlays: FlowCheckOverlay[] };
export type FlowCheckDiagnostic = {
  uri: string;
  start: number;
  end: number;
  message: string;
  code: "lowering" | "bend-parsing" | "checking" | "holes";
};
export type FlowTypedHover = { start: number; end: number; value: string };
export type FlowValuePreview = { uri: string; offset: number; value: string };
export type FlowCheckResult = {
  id: number;
  uri: string;
  version: number;
  diagnostics: FlowCheckDiagnostic[];
  hovers: Record<string, string>;
  typedHovers: FlowTypedHover[];
  valuePreviews: FlowValuePreview[];
};
