import assert from "node:assert/strict";
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import * as path from "node:path";
import test from "node:test";
import { pathToFileURL } from "node:url";
import { flowDefinitionAt, flowProjectDefinitionAt } from "../index.js";

function at(source: string, needle: string, occurrence = 0): number {
  let offset = -1;
  for (let index = 0; index <= occurrence; index++) offset = source.indexOf(needle, offset + 1);
  assert.notEqual(offset, -1);
  return offset;
}

test("navigates to top-level Flow declarations", () => {
  const source = `List<T: Data>: Data =\n  | Nil{}\n  | Cons{T, List<T>}\n\nxs: List<Nat> = Nil\n`;
  const use = at(source, "List<Nat>");
  const found = flowDefinitionAt(source, use + 2);
  assert.deepEqual(found, { start: at(source, "List"), end: at(source, "List") + 4 });
});

test("navigates to constructor declarations", () => {
  const source = `List<T: Data>: Data =\n  | Nil{}\n  | Cons{T, List<T>}\n\nxs: List<Nat> = Cons<Nat>{2n, Nil}\n`;
  const consUse = at(source, "Cons<Nat>");
  const nilUse = source.lastIndexOf("Nil");
  assert.deepEqual(flowDefinitionAt(source, consUse + 1), {
    start: at(source, "Cons"), end: at(source, "Cons") + 4,
  });
  assert.deepEqual(flowDefinitionAt(source, nilUse + 1), {
    start: at(source, "Nil"), end: at(source, "Nil") + 3,
  });
});

test("navigates to parameters and recursive functions", () => {
  const source = `sum(xs: List<Nat>): Nat =\n  match xs:\n    | Nil => 0n\n    | Cons{x, tail} => sum(tail)\n`;
  const parameter = at(source, "xs");
  assert.deepEqual(flowDefinitionAt(source, at(source, "xs", 1) + 1), {
    start: parameter, end: parameter + 2,
  });
  assert.deepEqual(flowDefinitionAt(source, at(source, "sum", 1) + 1), {
    start: at(source, "sum"), end: at(source, "sum") + 3,
  });
  const tailDefinition = at(source, "tail");
  assert.deepEqual(flowDefinitionAt(source, at(source, "tail", 1) + 1), {
    start: tailDefinition, end: tailDefinition + 4,
  });
});

test("respects Flow's definition order", () => {
  const source = `first: Nat = later\nlater: Nat = 0n\n`;
  assert.equal(flowDefinitionAt(source, at(source, "later") + 1), null);
});

test("navigates to explicitly imported Base definitions", () => {
  const root = mkdtempSync(path.join(tmpdir(), "flow-base-nav-"));
  try {
    const source = `import Base\nvalue: Nat = 0n\n`;
    const entry = path.join(root, "main.flow");
    writeFileSync(entry, source);
    const found = flowProjectDefinitionAt(entry, pathToFileURL(entry).href, source, source.indexOf("Nat") + 1);
    assert.ok(found?.uri.endsWith("/base.bend"));
    assert.ok((found?.range.end ?? 0) > (found?.range.start ?? 0));
  } finally { rmSync(root, { recursive: true, force: true }); }
});

test("navigates through relative Flow imports", () => {
  const root = mkdtempSync(path.join(tmpdir(), "flow-nav-"));
  try {
    const library = `answer(): Nat = 42n\n`;
    const source = `import ./library.flow as Lib\nmain(): Nat = Lib.answer()\n`;
    const entry = path.join(root, "main.flow");
    const imported = path.join(root, "library.flow");
    writeFileSync(entry, source);
    writeFileSync(imported, library);
    const found = flowProjectDefinitionAt(entry, pathToFileURL(entry).href, source, source.indexOf("Lib.answer") + 5);
    assert.deepEqual(found, {
      uri: pathToFileURL(imported).href,
      range: { start: library.indexOf("answer"), end: library.indexOf("answer") + 6 },
    });
  } finally { rmSync(root, { recursive: true, force: true }); }
});

test("navigates to original Flow sources in hash hub packages", () => {
  const root = mkdtempSync(path.join(tmpdir(), "flow-hub-source-"));
  const previous = process.env.BEND_LIB;
  process.env.BEND_LIB = root;
  try {
    const moduleDirectory = path.join(root, "0xabc123");
    const imported = path.join(moduleDirectory, "library.flow");
    const library = `answer(): Nat = 42n\n`;
    const entry = path.join(root, "main.flow");
    const source = `import 0xabc123/library.flow as Lib\nmain(): Nat = Lib.answer()\n`;
    writeFileSync(entry, source);
    mkdirSync(moduleDirectory, { recursive: true });
    writeFileSync(imported, library);
    const found = flowProjectDefinitionAt(entry, pathToFileURL(entry).href, source, source.indexOf("Lib.answer") + 5);
    assert.equal(found?.uri, pathToFileURL(imported).href);
    assert.deepEqual(found?.range, { start: library.indexOf("answer"), end: library.indexOf("answer") + 6 });
  } finally {
    if (previous === undefined) delete process.env.BEND_LIB; else process.env.BEND_LIB = previous;
    rmSync(root, { recursive: true, force: true });
  }
});

test("navigates through hash hub imports", () => {
  const root = mkdtempSync(path.join(tmpdir(), "flow-hub-"));
  const previous = process.env.BEND_LIB;
  process.env.BEND_LIB = root;
  try {
    const moduleDirectory = path.join(root, "0xabcdef");
    const imported = path.join(moduleDirectory, "library.bend");
    const library = `def answer() -> Nat:\n  42n\n`;
    const entry = path.join(root, "main.flow");
    const source = `import 0xabcdef/library.bend as Lib\nmain(): Nat = Lib.answer()\n`;
    writeFileSync(entry, source);
    mkdirSync(moduleDirectory, { recursive: true });
    writeFileSync(imported, library);
    const found = flowProjectDefinitionAt(entry, pathToFileURL(entry).href, source, source.indexOf("Lib.answer") + 5);
    assert.equal(found?.uri, pathToFileURL(imported).href);
    assert.deepEqual(found?.range, { start: library.indexOf("answer"), end: library.indexOf("answer") + 6 });
  } finally {
    if (previous === undefined) delete process.env.BEND_LIB; else process.env.BEND_LIB = previous;
    rmSync(root, { recursive: true, force: true });
  }
});

test("navigates inside dependent fields", () => {
  const source = `MyProp<n: Nat>: Type =\n  | eq{k: Nat, k == n}\n`;
  const kDefinition = at(source, "k:");
  const kUse = at(source, "k ==");
  assert.deepEqual(flowDefinitionAt(source, kUse), { start: kDefinition, end: kDefinition + 1 });
  const nDefinition = at(source, "n:");
  const nUse = source.lastIndexOf("n");
  assert.deepEqual(flowDefinitionAt(source, nUse), { start: nDefinition, end: nDefinition + 1 });
});
