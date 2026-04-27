# Orb Oracle Formalization

This repository contains a Rocq 8.18.0 formalization of the Orb Oracle protocol.
[Oracle.v] is documented and organized to reference the Orb Oracle paper.

## Files

- `Oracle.v`: main Rocq development

## Build

To compile the development:

```sh
coqc Oracle.v
```
To generate HTML documentation and a table of contents: 

```sh
coqdoc --parse-comments --table-of-contents Oracle.v
```

To clean generated files:

```sh
rm -f *.glob *.vo *.vos *.vok *.html *.css
```

## Installing Rocq

We used Rocq/Coq 8.18.0 for this formalization.

General installation instructions are available at the Rocq website:
https://rocq-prover.org/install#linux-rocqide

Readers should install version 8.18.0 (for example via an opam switch), since newer versions may introduce incompatibilities.

We recommend the standalone IDE RocqIDE, or the VS Code extension VsCoq.

Installing Rocq allows the reader to step through the proofs.
