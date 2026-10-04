import assert from "node:assert/strict";
import test from "node:test";
import { tokenizeBend } from "../semantic-tokens.js";

test("classifies core Bend syntax", () => {
  const source = `# comment\ndef add(x: Nat) -> Nat:\n  Nat.add(x, 1n)\n`;
  const tokens = tokenizeBend(source).map((token) => ({ text: source.slice(token.start, token.start + token.length), type: token.type }));
  assert.deepEqual(tokens.filter((token) => ["# comment", "def", "add", "Nat", "Nat.add", "1n"].includes(token.text)), [
    { text: "# comment", type: "comment" },
    { text: "def", type: "keyword" },
    { text: "add", type: "function" },
    { text: "Nat", type: "type" },
    { text: "Nat", type: "type" },
    { text: "Nat.add", type: "function" },
    { text: "1n", type: "number" },
  ]);
});

test("does not color comment contents as code", () => {
  const source = `# def fake()\ndef real() -> U32:\n  0\n`;
  const tokens = tokenizeBend(source);
  assert.equal(tokens.filter((token) => token.type === "function").length, 1);
  assert.equal(source.slice(tokens.find((token) => token.type === "function")!.start, tokens.find((token) => token.type === "function")!.start + 4), "real");
});
