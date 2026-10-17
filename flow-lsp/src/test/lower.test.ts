import assert from "node:assert/strict";
import test from "node:test";
import { lowerFlow, originalFlowSpan } from "../index.js";

test("lowers Flow types, constructors, functions, and matches to Bend", () => {
  const source = `List<T: Data>: Data =\n  | Nil{}\n  | Cons{T, List<T>}\n\nexample: List<Nat> = Cons<Nat>{2n, Nil}\n\nsum(ls: List<Nat>): Nat =\n  match ls:\n    | Nil => 0n\n    | Cons{x, xs} => sum(xs)\n`;
  const lowered = lowerFlow(source);
  assert.match(lowered.bend, /type List<T: Data> is Data:/);
  assert.match(lowered.bend, /Cons\{field0: T, field1: List<T>\}/);
  assert.match(lowered.bend, /\{Cons\{2n, Nil\{\}\} : List<Nat>\}/);
  assert.match(lowered.bend, /def sum\(ls: List<Nat>\) -> Nat:/);
  assert.match(lowered.bend, /case Cons\{x, xs\}:/);
});

test("allows newlines throughout type constructors", () => {
  const lowered = lowerFlow(`DB<i: Index>: Data =\n  | mk {\n      get: (\n        k: String\n      ) -> i(k),\n      count: Nat\n    }\n\nmake<i: Index>(get: (k: String) -> i(k)): DB<i> =\n  mk<i>{\n    get,\n    0n\n  }\n`);
  assert.match(lowered.bend, /mk\{get: @k: String -> i\(k\), count: Nat\}/);
  assert.match(lowered.bend, /\{mk\{get, 0n\} : DB<i>\}/);
});

test("lowers indexed types and dependent function fields", () => {
  const lowered = lowerFlow(`DB<i: Index>: Data =\n  | mk {get: (k: String) -> i(k)}\n`);
  assert.match(lowered.bend, /type DB<i: Index> is Data:/);
  assert.match(lowered.bend, /mk\{get: @k: String -> i\(k\)\}/);
});

test("preserves pair types and quantity terms", () => {
  const lowered = lowerFlow(`PairValue: Type = Nat & String\nMeet: Quant = &1 <&> &2\nReusable: Quant = &2\n`);
  assert.match(lowered.bend, /def PairValue\(\) -> Type:\n  Nat & String/);
  assert.match(lowered.bend, /def Meet\(\) -> Quant:\n  &1 <&> &2/);
  assert.match(lowered.bend, /def Reusable\(\) -> Quant:\n  &2/);
});

test("creates a constructor for dependent tuple types", () => {
  const lowered = lowerFlow(`FIN: Type = (x: Nat, x == 4n)\n`);
  assert.match(lowered.bend, /type FIN is Type:/);
  assert.match(lowered.bend, /FIN\.mk\{x: Nat, proof: \{x == 4n : Nat\}\}/);
});

test("lifts nested type and function declarations", () => {
  const lowered = lowerFlow(`sample: Nat =\n  Flag: Type = | On{} | Off{}\n  choose(flag: Flag): Nat =\n    match flag:\n      | On => 1n\n      | Off => 0n\n  value: Flag = On\n  choose(value)\n`);
  assert.match(lowered.bend, /type sample\.Flag is Type:/);
  assert.match(lowered.bend, /sample\.Flag\.On\{\}/);
  assert.match(lowered.bend, /def sample\.choose\(flag: sample\.Flag\) -> Nat:/);
  assert.match(lowered.bend, /value: sample\.Flag = sample\.Flag\.On\{\}/);
  assert.match(lowered.bend, /sample\.choose\(value\)/);
});

test("lifts local block expressions with their free variables", () => {
  const lowered = lowerFlow(`import Base\nchoose(flag: Bool): Nat =\n  value: Nat =\n    match flag:\n      | True{} => 1n\n      | False{} => 0n\n  value\n`);
  assert.match(lowered.bend, /def choose\.value\(flag: Bool\) -> Nat:\n\s+match flag:/);
  assert.match(lowered.bend, /case True\{\}:/);
  assert.match(lowered.bend, /value: Nat = choose\.value\(flag\)/);
});

test("does not import Base implicitly", () => {
  assert.doesNotMatch(lowerFlow(`value: Type = Type\n`).bend, /import Base/);
  assert.match(lowerFlow(`import Base\nvalue: Nat = 0n\n`).bend, /^import Base/);
});

test("rewrites relative and hub Flow imports to Bend", () => {
  const lowered = lowerFlow(`import ./math.flow as Math\nimport 0xabcdef/lib.flow as Lib\nmain(): Nat = Math.answer()\n`);
  assert.match(lowered.bend, /import \.\/math\.bend as Math/);
  assert.match(lowered.bend, /import 0xabcdef\/lib\.bend as Lib/);
});

test("preserves do notation and explicit equality proofs", () => {
  const lowered = lowerFlow(`import Base\nrefl(+a: Nat): {a == a : Nat} = {==}\nmain(): IO(Unit) =\n  do IO<Unit>:\n    IO.print(\"hello\")\n`);
  assert.match(lowered.bend, /def refl\(\+a: Nat\) -> \{a == a : Nat\}:\n  \{==\}/);
  assert.match(lowered.bend, /def main\(\) -> IO\(Unit\):\n  do IO<Unit>:\n    IO\.print\("hello"\)/);
});

test("preserves Bend quantity markers", () => {
  const lowered = lowerFlow(`use(~T: Data, +value: T, -proof: Type): T =\n  +copy: T = value\n  copy\n`);
  assert.match(lowered.bend, /def use\(~T: Data, \+value: T, -proof: Type\) -> T:/);
  assert.match(lowered.bend, /\+copy: T = value/);
});

test("maps generated offsets back to Flow", () => {
  const source = `value: Nat = 1n\n`;
  const lowered = lowerFlow(source);
  const generated = lowered.bend.indexOf("1n");
  assert.deepEqual(originalFlowSpan(lowered, generated), { start: source.indexOf("1n"), end: source.indexOf("1n") + 2 });
});
