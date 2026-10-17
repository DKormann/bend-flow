import assert from "node:assert/strict";
import { mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import * as path from "node:path";
import { pathToFileURL } from "node:url";
import test from "node:test";
import { checkBend } from "../checker-core.js";

async function check(source: string) {
  const root = await mkdtemp(path.join(tmpdir(), "bend-checker-test-"));
  const file = path.join(root, "main.bend");
  const uri = pathToFileURL(file).href;
  await writeFile(file, source);
  try {
    return await checkBend({
      id: 1,
      uri,
      path: file,
      version: 1,
      overlays: [{ path: file, uri, text: source, version: 1 }],
    });
  } finally {
    await rm(root, { recursive: true, force: true });
  }
}

test("accepts a well-typed Bend document", async () => {
  const result = await check(`import Base\n\ndef identity(x: Nat) -> Nat:\n  x\n`);
  assert.deepEqual(result.diagnostics, []);
  assert.match(result.hovers.identity, /identity :/);
  assert.match(result.hovers.Nat, /```bend/);
  assert.ok(result.typedHovers.some((hover) => /x : Nat/.test(hover.value)));
});

test("previews marked pure top-level values", async () => {
  const result = await check(`import Base\n\ndef answer() -> U32:\n  (40 + 2 : U32)\n  #?\n`);
  assert.deepEqual(result.diagnostics, []);
  assert.equal(result.valuePreviews.length, 1);
  assert.equal(result.valuePreviews[0].value, "42");
});

test("previews an explicitly named top-level value", async () => {
  const result = await check(`import Base\n\ndef answer() -> U32:\n  42\n\n#? answer\n`);
  assert.deepEqual(result.diagnostics, []);
  assert.equal(result.valuePreviews[0].value, "42");
});

test("previews pure calls in a marker", async () => {
  const result = await check(`import Base\n\ndef add(x: Nat, y: Nat) -> Nat:\n  (x + y : Nat)\n\n#? add(3n, 4n)\n`);
  assert.deepEqual(result.diagnostics, []);
  assert.equal(result.valuePreviews.length, 1);
  assert.equal(result.valuePreviews[0].value, "7n");
});

test("does not preview functions", async () => {
  const result = await check(`import Base\n\ndef identity(x: U32) -> U32:\n  x\n  #?\n`);
  assert.deepEqual(result.diagnostics, []);
  assert.deepEqual(result.valuePreviews, []);
});

test("reports Bend type checker errors", async () => {
  const result = await check(`import Base\n\ndef wrong() -> Nat:\n  0\n`);
  assert.equal(result.diagnostics.length, 1);
  assert.equal(result.diagnostics[0].code, "checking");
  assert.match(result.diagnostics[0].message, /Nat|U32/);
});

test("reports unresolved holes", async () => {
  const result = await check(`import Base\n\ndef unfinished() -> Nat:\n  ?TODO\n`);
  assert.equal(result.diagnostics.length, 1);
  assert.equal(result.diagnostics[0].code, "holes");
  assert.match(result.diagnostics[0].message, /TODO/);
});
