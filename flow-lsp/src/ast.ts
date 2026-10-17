export type Span = { start: number; end: number };

export type Identifier = { kind: "Identifier"; name: string; span: Span };

export type Quantity = "none" | "lone" | "many" | "comptime";

export type Field = {
  kind: "Field";
  name?: Identifier;
  quantity: Quantity;
  quantitySpan?: Span;
  type: Expression;
  span: Span;
};

export type Variant = {
  kind: "Variant";
  name: Identifier;
  fields: Field[];
  span: Span;
};

export type NameExpression = Identifier;
export type NumberExpression = { kind: "NumberExpression"; value: string; span: Span };
export type StringExpression = { kind: "StringExpression"; value: string; raw: string; span: Span };
export type ArrowExpression = { kind: "ArrowExpression"; domain: Expression; codomain: Expression; span: Span };
export type EqualityExpression = { kind: "EqualityExpression"; left: Expression; right: Expression; span: Span };
export type BinaryExpression = { kind: "BinaryExpression"; operator: "&" | "<&>" | "<>" | "+"; left: Expression; right: Expression; span: Span };
export type QuantExpression = { kind: "QuantExpression"; value: "&0" | "&1" | "&2"; span: Span };
export type PrefixQuantityExpression = { kind: "PrefixQuantityExpression"; quantity: Quantity; quantitySpan: Span; value: Expression; span: Span };
export type ListExpression = { kind: "ListExpression"; values: Expression[]; span: Span };
export type ArrayExpression = { kind: "ArrayExpression"; value: Expression; type: Expression; size: Expression; mode: "count" | "depth"; span: Span };
export type IndexExpression = { kind: "IndexExpression"; target: Expression; index: Expression; span: Span };
export type ArraySetExpression = { kind: "ArraySetExpression"; target: Expression; index: Expression; value: Expression; span: Span };
export type RewriteExpression = { kind: "RewriteExpression"; proof: Expression; motive: Expression; value: Expression; span: Span };
export type TypedEqualityExpression = { kind: "TypedEqualityExpression"; left: Expression; right: Expression; type: Expression; span: Span };
export type ReflexivityExpression = { kind: "ReflexivityExpression"; span: Span };
export type AnnotationExpression = { kind: "AnnotationExpression"; value: Expression; type: Expression; span: Span };
export type CallExpression = { kind: "CallExpression"; callee: Expression; arguments: Expression[]; span: Span };
export type TypeApplicationExpression = { kind: "TypeApplicationExpression"; callee: Expression; arguments: Expression[]; span: Span };
export type ConstructorExpression = { kind: "ConstructorExpression"; callee: Expression; arguments: Expression[]; span: Span };
export type TupleExpression = { kind: "TupleExpression"; fields: Field[]; span: Span };
export type UnionExpression = { kind: "UnionExpression"; variants: Variant[]; span: Span };
export type MatchExpression = { kind: "MatchExpression"; scrutinee: Expression; cases: MatchCase[]; span: Span };
export type DoStatement = { kind: "DoStatement"; source: string; span: Span };
export type DoExpression = { kind: "DoExpression"; effect: Expression; statements: DoStatement[]; span: Span };

export type Expression =
  | NameExpression
  | NumberExpression
  | StringExpression
  | ArrowExpression
  | EqualityExpression
  | BinaryExpression
  | QuantExpression
  | PrefixQuantityExpression
  | ListExpression
  | ArrayExpression
  | IndexExpression
  | ArraySetExpression
  | RewriteExpression
  | TypedEqualityExpression
  | ReflexivityExpression
  | AnnotationExpression
  | CallExpression
  | TypeApplicationExpression
  | ConstructorExpression
  | TupleExpression
  | UnionExpression
  | MatchExpression
  | DoExpression;

export type NamePattern = { kind: "NamePattern"; name: string; quantity?: Quantity; quantitySpan?: Span; span: Span };
export type ConstructorPattern = {
  kind: "ConstructorPattern";
  constructor: string;
  typeArguments: Expression[];
  fields: Pattern[];
  span: Span;
};
export type LiteralPattern = { kind: "LiteralPattern"; raw: string; span: Span };
export type NatAddPattern = { kind: "NatAddPattern"; amount: string; rest: Pattern; span: Span };
export type Pattern = NamePattern | ConstructorPattern | LiteralPattern | NatAddPattern;

export type MatchCase = {
  kind: "MatchCase";
  pattern: Pattern;
  body: Expression | Block;
  span: Span;
};

export type Declaration = {
  kind: "Declaration";
  name: Identifier;
  quantity: Quantity;
  quantitySpan?: Span;
  typeParameters: Field[];
  parameters: Field[];
  returnType: Expression;
  body: Expression | Block;
  span: Span;
};

export type ImportStatement = {
  kind: "ImportStatement";
  path: string;
  alias?: Identifier;
  pathSpan: Span;
  span: Span;
};

export type RawBendDefinition = {
  kind: "RawBendDefinition";
  source: string;
  span: Span;
};

export type ExpressionStatement = {
  kind: "ExpressionStatement";
  expression: Expression;
  span: Span;
};

export type PatternDeclaration = {
  kind: "PatternDeclaration";
  pattern: Pattern;
  value: Expression;
  span: Span;
};

export type Statement = ImportStatement | Declaration | RawBendDefinition | ExpressionStatement | PatternDeclaration;
export type Block = { kind: "Block"; statements: Statement[]; span: Span };
export type Program = { kind: "Program"; statements: Statement[]; span: Span };
