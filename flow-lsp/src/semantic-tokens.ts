export const FLOW_TOKEN_TYPES = ["type", "function", "variable", "parameter", "keyword", "comment", "string", "number", "operator"] as const;
export const FLOW_TOKEN_MODIFIERS = ["declaration", "definition", "readonly"] as const;

export type FlowSemanticToken = {
  start: number;
  length: number;
  type: (typeof FLOW_TOKEN_TYPES)[number];
  modifiers?: Array<(typeof FLOW_TOKEN_MODIFIERS)[number]>;
};

const KEYWORDS = new Set(["match", "def", "law", "type", "is", "case", "do", "return", "for", "exs", "where", "import", "as"]);
const BUILTIN_TYPES = new Set(["Type", "Data", "Kind", "Quant", "Nat", "U32", "F32", "String", "Bool"]);

export function tokenizeFlow(source: string): FlowSemanticToken[] {
  const result: FlowSemanticToken[] = [];
  let offset = 0;
  let lineStart = true;
  const push = (start: number, end: number, type: FlowSemanticToken["type"], modifiers?: FlowSemanticToken["modifiers"]): void => {
    result.push({ start, length: end - start, type, modifiers });
  };

  while (offset < source.length) {
    const char = source[offset];
    if (char === "\n") { lineStart = true; offset++; continue; }
    if (/\s/.test(char)) { offset++; continue; }
    if (char === "#") {
      const end = source.indexOf("\n", offset);
      const stop = end < 0 ? source.length : end;
      push(offset, stop, "comment");
      offset = stop;
      continue;
    }
    if (char === '"' || char === "'") {
      const quote = char;
      let end = offset + 1;
      while (end < source.length) {
        if (source[end] === "\\") end += 2;
        else if (source[end++] === quote) break;
        else if (source[end - 1] === "\n") break;
      }
      push(offset, Math.min(end, source.length), "string");
      offset = end;
      lineStart = false;
      continue;
    }
    if (/[0-9]/.test(char)) {
      const match = /^(?:[0-9]+\.[0-9]+(?:[eE][+-]?[0-9]+)?|[0-9]+n?)/.exec(source.slice(offset))!;
      push(offset, offset + match[0].length, "number");
      offset += match[0].length;
      lineStart = false;
      continue;
    }
    if (/[A-Za-z_]/.test(char)) {
      const match = /^[A-Za-z_][A-Za-z0-9_.]*/.exec(source.slice(offset))!;
      const word = match[0];
      const end = offset + word.length;
      let cursor = end;
      while (cursor < source.length && /[ \t]/.test(source[cursor])) cursor++;
      const isDeclaration = lineStart && (source[cursor] === ":" || source[cursor] === "(" || source[cursor] === "<");
      if (KEYWORDS.has(word)) push(offset, end, "keyword");
      else if (isDeclaration) {
        const header = source.slice(end, source.indexOf("\n", end) < 0 ? source.length : source.indexOf("\n", end));
        const typeLike = header.trimStart().startsWith("<") || /:\s*(?:Type|Data|Kind)\s*=/.test(header);
        push(offset, end, typeLike ? "type" : header.trimStart().startsWith("(") ? "function" : "variable", ["declaration", "definition"]);
      } else if (BUILTIN_TYPES.has(word)) push(offset, end, "type", ["readonly"]);
      else if (/^[A-Z]/.test(word)) push(offset, end, "type");
      else if (source[cursor] === "(") push(offset, end, "function");
      else push(offset, end, "variable");
      offset = end;
      lineStart = false;
      continue;
    }
    const pair = source.slice(offset, offset + 2);
    const operator = ["->", "=>", "==", "!=", "<=", ">=", "<-"].includes(pair) ? pair
      : /[|<>{}=:+\-*\/%&!~]/.test(char) ? char : null;
    if (operator) {
      const declarationMarker: boolean = lineStart && /^[+\-~]$/.test(operator);
      push(offset, offset + operator.length, "operator");
      offset += operator.length;
      lineStart = declarationMarker;
      continue;
    }
    offset++;
    lineStart = false;
  }
  return result;
}
