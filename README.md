# Bend & Flow language tools

Language tooling for Bend 2 and the Flow superset.

## Current milestone: Bend

- `bend-lsp/` contains the Bend language server.
- `flow-lsp/` contains the source-spanned Flow parser, Bend lowering pass, source maps, and Flow language server.
- `vscode-extension/` contains the VS Code client and TextMate grammar.
- `vendor/bend2/` contains the pinned Bend 2 compiler infrastructure used by the server.

The Bend server currently provides compiler-backed diagnostics, semantic coloring, and Go to Definition. Diagnostics run Bend's own `book_load` and `book_valid` in a worker thread, including unsaved imported files. The VS Code extension also ships a TextMate grammar so coloring remains available while the server starts or while source is temporarily incomplete.

## Build and test

Node.js 20 or newer is required.

```sh
npm install
npm run build
npm test
```

To create a VS Code package:

```sh
npm run package:vscode
```
