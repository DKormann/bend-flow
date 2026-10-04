# Bend & Flow Language Tools

VS Code support for Bend 2 and Flow. It provides:

- syntax and semantic coloring for `.bend` and `.flow` files;
- parser diagnostics, cross-file Go to Definition, and Bend type previews for Flow;
- semantic highlighting from `bend-lsp`;
- compiler-accurate parsing and type-checking diagnostics;
- diagnostics for unresolved holes;
- Go to Definition for definitions, laws, types, constructors, imported symbols, and local binders;
- Bend type previews for definitions, types, constructors, parameters, and local variables;
- inline computed-value previews for pure, argument-free top-level Bend definitions marked with `#?`.

Add `#?` inside or immediately after a top-level definition to preview its normal form:

```bend
def answer() -> U32:
  42
  #?
```

VS Code displays this as `#? 42`; the second `42` is an editor inlay and is not written to the file. A standalone named marker such as `#? answer` is also supported. Functions, foreign definitions, effects, invalid programs, and definitions containing holes are not evaluated.

Bend navigation and diagnostics use the Bend 2 compiler vendored with this repository. Relative imports and cached hash/named hub imports support navigation from paths, aliases, and qualified symbols. Unsaved open files are supplied to the server as overlays, and checking runs in a worker so it does not block editor requests. Flow files are lowered to native Bend programs and checked by Bend itself in a worker; Bend diagnostics are source-mapped back to Flow. Flow also provides scope-aware navigation for declarations, constructors, parameters, pattern bindings, and dependent fields.

## Development

From the repository root:

```sh
npm install
npm run build
npm test
npm run package:vscode
```

Press `F5` from the extension directory in VS Code, or install the generated `.vsix` file.
