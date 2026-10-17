# Flow parser

The Flow frontend. It parses Flow into a source-spanned AST, structurally lowers that AST to canonical Bend, and delegates semantic validation to Bend's native parser and type checker.

Supported syntax currently includes:

- value and function declarations, including multiline function argument lists;
- Bend quantity markers on parameters, locals, and pattern binders (`+x`, `-x`, and `~x`), quantity terms (`&0`, `&1`, `&2`), and quantity meet (`a <&> b`);
- explicit generic parameters (`List<T: Data>`);
- calls, type applications, and constructor expressions, with multiline delimiter contents;
- shorthand patterns and destructuring for Nat (`0n`, `1n+rest`), String literals, lists (`head <> tail`), and tuples (`(a, b)` and `(a, b) = pair`), plus list literals and array syntax (`[a, b]`, `[value : T*count]`, `[value : T^depth]`, `array[index]`, and `array[index] <- value`);
- tagged unions with named or unnamed fields;
- pair types (`A & B`), tuple values and patterns (`(a, b)`), dependent tuple types, dependent function fields (`(x: A) -> B(x)`), equality proofs (`{a == b : T}` and `{==}`), and Bend rewrites (`%proof : motive; value` or a newline in place of `;`);
- indentation-based blocks, matches, and Bend `do Effect<T>:` notation, including block-valued local lets lifted with their free variables;
- matches on computed Flow values, automatically lifted through helper parameters to satisfy Bend's scrutinee restriction;
- nested declarations and inline unions;
- relative Flow/Bend imports and Bend hash or named hub imports;
- embedded top-level Bend `def`, `type`, and `law` declarations;
- comments, strings, numbers, arrows, and equality expressions.

```ts
import { parseFlow } from "flow-lsp";

const program = parseFlow(source);
```

`FlowParseError` contains an offset-based source span suitable for LSP diagnostics.

```ts
import { lowerFlow } from "flow-lsp";

const { bend, mappings } = lowerFlow(source);
```

The Flow language server lowers valid documents, loads the generated project graph with Bend's `book_load`, checks the native Bend `Book` with `book_valid`, and maps Bend diagnostics back through `mappings` to the original Flow source. Go to Definition follows aliases into relative Flow/Bend files and cached hash or named hub packages. Hover types are propagated through local declarations and pair (`Tuple`) pattern bindings.

Flow does not import `Base` implicitly. A file using `Nat`, `List`, `IO`, or other Base declarations must begin with `import Base`; this also enables Go to Definition into `base.bend`.

A Flow hub package should include both `module.flow` and its lowered `module.bend`. A Flow import names the source file (`import 0x…/module.flow as Module`); checking rewrites it to `module.bend`, while navigation opens the original `module.flow`. Bend's package download caches the complete manifest, including the Flow source.
