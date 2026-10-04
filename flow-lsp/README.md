# Flow parser

The Flow frontend. It parses Flow into a source-spanned AST, structurally lowers that AST to canonical Bend, and delegates semantic validation to Bend's native parser and type checker.

Supported syntax currently includes:

- value and function declarations;
- Bend quantity markers on parameters and local variables (`+x`, `-x`, and `~x`);
- explicit generic parameters (`List<T: Data>`);
- calls, type applications, and constructor expressions;
- tagged unions with named or unnamed fields;
- dependent single-constructor tuple types and equality proofs (`{a == b : T}` and `{==}`);
- indentation-based blocks, matches, and Bend `do Effect<T>:` notation, including block-valued local lets lifted with their free variables;
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

The Flow language server lowers valid documents, loads the generated project graph with Bend's `book_load`, checks the native Bend `Book` with `book_valid`, and maps Bend diagnostics back through `mappings` to the original Flow source. Go to Definition follows aliases into relative Flow/Bend files and cached hash or named hub packages.

Flow does not import `Base` implicitly. A file using `Nat`, `List`, `IO`, or other Base declarations must begin with `import Base`; this also enables Go to Definition into `base.bend`.

A Flow hub package should include both `module.flow` and its lowered `module.bend`. A Flow import names the source file (`import 0x…/module.flow as Module`); checking rewrites it to `module.bend`, while navigation opens the original `module.flow`. Bend's package download caches the complete manifest, including the Flow source.
