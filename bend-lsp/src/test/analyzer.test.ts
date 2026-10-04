import assert from "node:assert/strict";
import { mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import * as path from "node:path";
import { pathToFileURL } from "node:url";
import test from "node:test";
import { definitionAt } from "../analyzer.js";

async function fixture(files: Record<string, string>): Promise<{ root: string; paths: Record<string, string> }> {
  const root = await mkdtemp(path.join(tmpdir(), "bend-lsp-test-"));
  const paths: Record<string, string> = {};
  for (const [name, text] of Object.entries(files)) {
    const file = path.join(root, name);
    paths[name] = file;
    await writeFile(file, text);
  }
  return { root, paths };
}

test("finds a top-level Bend definition", async (t) => {
  const source = `def double(x: Nat) -> Nat:\n  x\n\ndef main() -> Nat:\n  double(2n)\n`;
  const { root, paths } = await fixture({ "main.bend": source });
  t.after(() => rm(root, { recursive: true, force: true }));
  const uri = pathToFileURL(paths["main.bend"]).href;
  const found = await definitionAt(paths["main.bend"], uri, source, source.lastIndexOf("double") + 2);
  assert.deepEqual(found, {
    uri,
    range: { start: source.indexOf("double"), end: source.indexOf("double") + "double".length },
  });
});

test("finds a parameter through Bend binder identities", async (t) => {
  const source = `def identity(value: Nat) -> Nat:\n  value\n`;
  const { root, paths } = await fixture({ "main.bend": source });
  t.after(() => rm(root, { recursive: true, force: true }));
  const uri = pathToFileURL(paths["main.bend"]).href;
  const use = source.lastIndexOf("value");
  const found = await definitionAt(paths["main.bend"], uri, source, use + 2);
  const declaration = source.indexOf("value");
  assert.deepEqual(found, { uri, range: { start: declaration, end: declaration + "value".length } });
});

test("finds explicitly imported Base definitions", async (t) => {
  const source = `import Base\n\ndef identity(x: Nat) -> Nat:\n  x\n`;
  const { root, paths } = await fixture({ "main.bend": source });
  t.after(() => rm(root, { recursive: true, force: true }));
  const uri = pathToFileURL(paths["main.bend"]).href;
  const found = await definitionAt(paths["main.bend"], uri, source, source.indexOf("Nat") + 1);
  assert.ok(found?.uri.endsWith("/base.bend"));
  assert.ok((found?.range.end ?? 0) > (found?.range.start ?? 0));
});

test("opens a relative import from its path and alias", async (t) => {
  const library = `def answer() -> Nat:\n  42n\n`;
  const source = `import lib.bend as Lib\n\ndef main() -> Nat:\n  Lib.answer()\n`;
  const { root, paths } = await fixture({ "main.bend": source, "lib.bend": library });
  t.after(() => rm(root, { recursive: true, force: true }));
  const uri = pathToFileURL(paths["main.bend"]).href;
  const targetUri = pathToFileURL(paths["lib.bend"]).href;
  assert.deepEqual(await definitionAt(paths["main.bend"], uri, source, source.indexOf("lib.bend") + 2), { uri: targetUri, range: { start: 0, end: 0 } });
  assert.deepEqual(await definitionAt(paths["main.bend"], uri, source, source.indexOf("Lib") + 1), { uri: targetUri, range: { start: 0, end: 0 } });
});

test("follows an imported namespace alias", async (t) => {
  const library = `def answer() -> Nat:\n  42n\n`;
  const source = `import lib.bend as Lib\n\ndef main() -> Nat:\n  Lib.answer()\n`;
  const { root, paths } = await fixture({ "main.bend": source, "lib.bend": library });
  t.after(() => rm(root, { recursive: true, force: true }));
  const uri = pathToFileURL(paths["main.bend"]).href;
  const found = await definitionAt(paths["main.bend"], uri, source, source.indexOf("Lib.answer") + 5);
  assert.deepEqual(found, {
    uri: pathToFileURL(paths["lib.bend"]).href,
    range: { start: library.indexOf("answer"), end: library.indexOf("answer") + "answer".length },
  });
});
