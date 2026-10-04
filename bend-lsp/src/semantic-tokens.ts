export const TOKEN_TYPES = [
  "namespace",
  "type",
  "function",
  "variable",
  "parameter",
  "keyword",
  "comment",
  "string",
  "number",
  "operator",
] as const;

export const TOKEN_MODIFIERS = ["declaration", "definition", "readonly"] as const;

export type BendSemanticToken = {
  start: number;
  length: number;
  type: (typeof TOKEN_TYPES)[number];
  modifiers?: Array<(typeof TOKEN_MODIFIERS)[number]>;
};

const KEYWORDS = new Set([
  "def", "law", "type", "is", "match", "case", "do", "return", "for", "exs", "where", "import", "as",
]);
const BUILTIN_TYPES = new Set(["Type", "Data", "Kind", "Quant"]);
const OPERATORS = ["<&>", "->", "=>", "<-", "==", "!=", "<=", ">=", "++", "<>", "&&", "||", "<<", ">>"];

function nextNonSpace(source: string, offset: number): string {
  while (offset < source.length && /\s/.test(source[offset])) offset++;
  return source[offset] ?? "";
}

export function tokenizeBend(source: string): BendSemanticToken[] {
  const result: BendSemanticToken[] = [];
  let offset = 0;
  let declaration: "function" | "type" | null = null;

  const push = (start: number, end: number, type: BendSemanticToken["type"], modifiers?: BendSemanticToken["modifiers"]): void => {
    result.push({ start, length: end - start, type, modifiers });
  };

  while (offset < source.length) {
    const char = source[offset];
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
      declaration = null;
      continue;
    }
    if (char === "@" && source.startsWith("@unsafe", offset)) {
      push(offset, offset + 7, "keyword");
      offset += 7;
      continue;
    }
    if (/[0-9]/.test(char)) {
      const match = /^(?:[0-9]+\.[0-9]+(?:[eE][+-]?[0-9]+)?|[0-9]+n?)/.exec(source.slice(offset))!;
      push(offset, offset + match[0].length, "number");
      offset += match[0].length;
      declaration = null;
      continue;
    }
    if (/[A-Za-z_]/.test(char)) {
      const match = /^[A-Za-z_][A-Za-z0-9_.]*/.exec(source.slice(offset))!;
      const word = match[0];
      const end = offset + word.length;
      if (KEYWORDS.has(word)) {
        push(offset, end, "keyword");
        declaration = word === "def" || word === "law" ? "function" : word === "type" ? "type" : null;
      } else if (declaration) {
        push(offset, end, declaration, ["declaration", "definition"]);
        declaration = null;
      } else if (BUILTIN_TYPES.has(word)) {
        push(offset, end, "type", ["readonly"]);
      } else if (nextNonSpace(source, end) === "(" || nextNonSpace(source, end) === "!") {
        push(offset, end, "function");
      } else if (/^[A-Z]/.test(word.split(".").at(-1) ?? word)) {
        push(offset, end, "type");
      } else {
        push(offset, end, "variable");
      }
      offset = end;
      continue;
    }
    const operator = OPERATORS.find((candidate) => source.startsWith(candidate, offset))
      ?? (/[-+*\/%<>=&|!@\\~]/.test(char) ? char : null);
    if (operator) {
      push(offset, offset + operator.length, "operator");
      offset += operator.length;
      continue;
    }
    offset++;
  }
  return result;
}
