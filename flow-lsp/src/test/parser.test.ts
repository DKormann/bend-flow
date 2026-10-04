import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import test from "node:test";
import { fileURLToPath } from "node:url";
import { FlowParseError, parseFlow, type Declaration } from "../index.js";

const examplePath = fileURLToPath(new URL("../../../examples/example.flow", import.meta.url));

function declaration(source: string): Declaration {
  const statement = parseFlow(source).statements[0];
  assert.equal(statement.kind, "Declaration");
  return statement as Declaration;
}

test("parses the complete Flow example", () => {
  const program = parseFlow(readFileSync(examplePath, "utf8"));
  assert.equal(program.kind, "Program");
  assert.ok(program.statements.filter((statement) => statement.kind === "Declaration").length >= 10);
  assert.equal(program.statements.filter((statement) => statement.kind === "RawBendDefinition").length, 1);
});

test("parses generic type declarations with unnamed constructor fields", () => {
  const list = declaration(`List<T: Data>: Data =\n  | Nil{}\n  | Cons{T, List<T>}\n`);
  assert.equal(list.name.name, "List");
  assert.equal(list.typeParameters[0].name?.name, "T");
  assert.equal(list.body.kind, "UnionExpression");
  if (list.body.kind !== "UnionExpression") return;
  assert.equal(list.body.variants[0].name.name, "Nil");
  assert.equal(list.body.variants[0].fields.length, 0);
  assert.equal(list.body.variants[1].name.name, "Cons");
  assert.equal(list.body.variants[1].fields.length, 2);
  assert.equal(list.body.variants[1].fields[0].name, undefined);
  assert.equal(list.body.variants[1].fields[1].type.kind, "TypeApplicationExpression");
});

test("parses dependent single-constructor tuple types", () => {
  const fin = declaration(`FIN: Type = (x: Nat, x == 4n)\n`);
  assert.equal(fin.body.kind, "TupleExpression");
  if (fin.body.kind !== "TupleExpression") return;
  assert.equal(fin.body.fields[0].name?.name, "x");
  assert.equal(fin.body.fields[1].type.kind, "EqualityExpression");
});

test("parses explicit constructor type arguments", () => {
  const value = declaration(`xs: List<Nat> = Cons<Nat>{2n, Nil}\n`);
  assert.equal(value.body.kind, "ConstructorExpression");
  if (value.body.kind !== "ConstructorExpression") return;
  assert.equal(value.body.callee.kind, "TypeApplicationExpression");
  assert.equal(value.body.arguments.length, 2);
});

test("parses match constructor patterns", () => {
  const sum = declaration(`sum(xs: List<Nat>): Nat =\n  match xs:\n    | Nil => 0n\n    | Cons{x, tail} => sum(tail)\n`);
  assert.equal(sum.body.kind, "Block");
  if (sum.body.kind !== "Block") return;
  const statement = sum.body.statements[0];
  assert.equal(statement.kind, "ExpressionStatement");
  if (statement.kind !== "ExpressionStatement" || statement.expression.kind !== "MatchExpression") return;
  assert.equal(statement.expression.cases[1].pattern.kind, "ConstructorPattern");
});

test("parses relative and hub imports", () => {
  const program = parseFlow(`import ./math.flow as Math\nimport 0xabcdef/lib.bend as Lib\n`);
  assert.equal(program.statements[0].kind, "ImportStatement");
  assert.equal(program.statements[1].kind, "ImportStatement");
  if (program.statements[0].kind !== "ImportStatement") return;
  assert.equal(program.statements[0].path, "./math.flow");
  assert.equal(program.statements[0].alias?.name, "Math");
});

test("parses do notation and equality proof terms", () => {
  const program = parseFlow(`import Base\nproof(+a: Nat, +b: Nat): {a == b : Nat} = {==}\nmain(): IO(Unit) =\n  do IO<Unit>:\n    text: String <- IO.pure(String, \"hello\")\n    IO.print(text)\n`);
  const proof = program.statements[1];
  assert.equal(proof.kind, "Declaration");
  if (proof.kind === "Declaration") {
    assert.equal(proof.returnType.kind, "TypedEqualityExpression");
    assert.equal(proof.body.kind, "ReflexivityExpression");
  }
  const main = program.statements[2];
  assert.equal(main.kind, "Declaration");
  if (main.kind === "Declaration" && main.body.kind === "Block") {
    const expression = main.body.statements[0];
    assert.equal(expression.kind, "ExpressionStatement");
    if (expression.kind === "ExpressionStatement" && expression.expression.kind === "DoExpression") {
      assert.equal(expression.expression.statements.length, 2);
    }
  }
});

test("parses Bend quantity markers on parameters and local variables", () => {
  const fn = declaration(`use(~T: Data, +value: T, -proof: Type): T =\n  +copy: T = value\n  copy\n`);
  assert.deepEqual(fn.parameters.map((field) => field.quantity), ["comptime", "many", "none"]);
  assert.equal(fn.body.kind, "Block");
  if (fn.body.kind !== "Block" || fn.body.statements[0].kind !== "Declaration") return;
  assert.equal(fn.body.statements[0].quantity, "many");
});

test("reports source spans for malformed input", () => {
  assert.throws(
    () => parseFlow(`List<T: Data: Data = Nil\n`),
    (error) => error instanceof FlowParseError && error.span.start >= 0,
  );
});
