import assert from "node:assert/strict";
import { mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import * as path from "node:path";
import { pathToFileURL } from "node:url";
import test from "node:test";
import { FlowChecker } from "../checker.js";

async function check(source: string) {
  const root = await mkdtemp(path.join(tmpdir(), "flow-checker-test-"));
  const file = path.join(root, "main.flow");
  const uri = pathToFileURL(file).href;
  await writeFile(file, source);
  const checker = new FlowChecker();
  try {
    return await checker.check({
      id: 1,
      uri,
      path: file,
      text: source,
      version: 1,
      overlays: [{ path: file, uri, text: source, version: 1 }],
    });
  } finally {
    await checker.close();
    await rm(root, { recursive: true, force: true });
  }
}

test("previews marked pure top-level Flow values", async () => {
  const result = await check(`import Base\n\nanswer: U32 = 42\n#?\n`);
  assert.deepEqual(result.diagnostics, []);
  assert.equal(result.valuePreviews.length, 1);
  assert.equal(result.valuePreviews[0].value, "42");
});

test("previews an explicitly named top-level Flow value", async () => {
  const result = await check(`import Base\n\nanswer: U32 = 42\n\n#? answer\n`);
  assert.deepEqual(result.diagnostics, []);
  assert.equal(result.valuePreviews[0].value, "42");
});

test("matches on a computed value", async () => {
  const result = await check(`import Base\n\npick(x: Bool): Bool = x\nmain(x: Bool): Nat =\n  match pick(x):\n    | True{} => 1n\n    | False{} => 0n\n`);
  assert.deepEqual(result.diagnostics, []);
});

test("accepts an explicitly typed computed match from Bend", async () => {
  const result = await check(`import Base\n\nf(~i: String): Type =\n  match {String.starts_with(i, "score:") : Bool}:\n    | True{} => Nat\n    | False{} => Unit\n`);
  assert.deepEqual(result.diagnostics, []);
});

test("lifts matches on computed local values", async () => {
  const result = await check(`import Base\n\nchoose(n: String): Type =\n  equal: Bool = String.eq(n, "setscore")\n  match equal:\n    | True{} => Nat\n    | False{} => Unit\n`);
  assert.deepEqual(result.diagnostics, []);
});

test("lifted nested matches capture outer pattern bindings used in types", async () => {
  const result = await check(`import Base\n\nNumber: Data = | ZERO{} | SUCC{Number}\nChoice<A: Type, B: Type>: Type = | left{A} | right{B}\nFamily(a: Number, b: Number): Type = Choice<{a == b : Number}, {b == a : Number}>\n@unsafe def sorry(-T: Type) -> T:\n  sorry(T)\nprove(+a: Number, +b: Number): Family(a, b) =\n  match a:\n    | ZERO{} => sorry(Family(a, b))\n    | SUCC{k} =>\n      inner: Family(k, b) = prove(k, b)\n      match inner:\n        | left{proof} => sorry(Family(a, b))\n        | right{proof} => sorry(Family(a, b))\n`);
  assert.deepEqual(result.diagnostics, []);
});

test("computed matches capture values used by their cases", async () => {
  const result = await check(`import Base\n\npick(x: Bool): Bool = x\nmain(x: Bool, yes: Nat, no: Nat): Nat =\n  match pick(x):\n    | True{} => yes\n    | False{} => no\n`);
  assert.deepEqual(result.diagnostics, []);
});

test("keeps lifted local functions after the aliases they use", async () => {
  const result = await check(`import Base\n\nIndex: Type = (-key: String) -> Type\nouter(index: Index): Type =\n  inner(value: Index): Type = Sigma<String, value>\n  inner(index)\n`);
  assert.deepEqual(result.diagnostics, []);
});

test("accepts newlines in function argument lists", async () => {
  const result = await check(`import Base\n\napply(\n  function: Bool -> Bool,\n  value: Bool\n): Bool =\n  function(value)\n\nchoose(\n  value: Bool,\n  whenTrue: Nat,\n  whenFalse: Nat\n): Nat =\n  match value:\n    | True{} => whenTrue\n    | False{} => whenFalse\n`);
  assert.deepEqual(result.diagnostics, []);
});

test("supports Bend equality rewrite syntax", async () => {
  const result = await check(`cast(-A: Type, -B: Type, equality: {A == B : Type}, value: A): B =\n  %equality : _; value\n\ncast.multiline(-A: Type, -B: Type, equality: {A == B : Type}, value: A): B =\n  %equality : _\n  value\n\ncong(-A: Type, a: A, b: A, P: A -> Type, equality: {a == b : A}): {P(a) == P(b) : Type} =\n  %equality : {P(a) == P(_) : Type}; {==}\n`);
  assert.deepEqual(result.diagnostics, []);
});

test("supports tuple destructuring declarations", async () => {
  const source = `import Base\n\nfg(t: Nat & Nat): Nat =\n  (a, b) = t\n  a\n`;
  const result = await check(source);
  assert.deepEqual(result.diagnostics, []);
  assert.ok(result.typedHovers.some((hover) => hover.start === source.indexOf("a,") && /a : Nat/.test(hover.value)));
  assert.ok(result.typedHovers.some((hover) => hover.start === source.lastIndexOf("a") && /a : Nat/.test(hover.value)));
});

test("supports tuple shorthand for values and patterns", async () => {
  const result = await check(`import Base\n\nFSignature: Type = List<Type> & Type\nsignature: FSignature = (Nil{}, Unit)\nresult(sig: FSignature): Type =\n  match sig:\n    | (inputs, output) => output\n`);
  assert.deepEqual(result.diagnostics, []);
});

test("provides types for pair pattern bindings", async () => {
  const source = `import Base\n\nFSignature: Type = Type & Type\nMethod(sig: FSignature): Type =\n  match sig:\n    | Tuple{a, b} => b\n`;
  const result = await check(source);
  assert.deepEqual(result.diagnostics, []);
  const a = source.indexOf("a, b");
  const b = source.indexOf("b}");
  assert.ok(result.typedHovers.some((hover) => hover.start === a && /a : Type/.test(hover.value)));
  assert.ok(result.typedHovers.some((hover) => hover.start === b && /b : Type/.test(hover.value)));
  assert.ok(result.typedHovers.some((hover) => hover.start === source.lastIndexOf("b") && /b : Type/.test(hover.value)));
});

test("provides types for constructor pattern bindings", async () => {
  const source = `import Base\n\nWrap<A: Type>: Type = | W{A}\nduplicate(value: Wrap<Nat>): Nat & Nat =\n  match value:\n    | W{+item} => (item, item)\n`;
  const result = await check(source);
  assert.deepEqual(result.diagnostics, []);
  const binding = source.indexOf("item}");
  assert.ok(result.typedHovers.some((hover) => hover.start === binding && /item : Nat/.test(hover.value)));
  assert.ok(result.typedHovers.some((hover) => hover.start === source.lastIndexOf("item") && /item : Nat/.test(hover.value)));
});

test("supports quantities on pattern bindings", async () => {
  const result = await check(`import Base\n\nNumber: Data = | ZERO{} | SUCC{Number}\nduplicate(value: Number): Number & Number =\n  match value:\n    | ZERO{} => Tuple{ZERO{}, ZERO{}}\n    | SUCC{+rest} => Tuple{rest, rest}\n`);
  assert.deepEqual(result.diagnostics, []);
});

test("checks Nat and String pattern shorthand", async () => {
  const result = await check(`import Base\n\npred(value: Nat): Nat =\n  match value:\n    | 0n => 0n\n    | 1n+rest => rest\nclassify(value: String): Nat =\n  match value:\n    | "" => 0n\n    | "ok" => 1n\n    | _ => 2n\n`);
  assert.deepEqual(result.diagnostics, []);
});

test("checks list cons operator syntax", async () => {
  const result = await check(`import Base\n\nprepend(head: Nat, tail: List<Nat>): List<Nat> = head <> tail\nfirst(values: List<Nat>): Nat =\n  match values:\n    | head <> tail => head\n    | Nil{} => 0n\n`);
  assert.deepEqual(result.diagnostics, []);
});

test("checks list and array syntax", async () => {
  const result = await check(`import Base\n\nlist: List<Nat> = [1n, 2n, 3n]\nmain(): Array<U32> & U32 =\n  array: Array<U32> = [0 : U32*8n]\n  array[5] <- 42\n  array[5]\n`);
  assert.deepEqual(result.diagnostics, []);
});

test("checks pair types and quantity terms", async () => {
  const result = await check(`import Base\n\npair(x: U32, y: U32): U32 & U32 = Tuple{x, y}\nquantity: Quant = &2\n`);
  assert.deepEqual(result.diagnostics, []);
});

test("does not preview Flow functions", async () => {
  const result = await check(`import Base\n\nidentity(x: U32): U32 = x\n#?\n`);
  assert.deepEqual(result.diagnostics, []);
  assert.deepEqual(result.valuePreviews, []);
});
