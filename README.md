# Orb Oracle Formalization

This repository contains a Rocq formalization of the Orb Oracle protocol, tested with Rocq 9.2.0.
[`Oracle.v`](Oracle.v) is documented and organized to reference the Orb Oracle paper.

## Files

- `Oracle.v`: main Rocq development

## Build

To compile:

```sh
rocq compile Oracle.v
```

To generate HTML documentation and a table of contents:

```sh
rocq doc --parse-comments --table-of-contents Oracle.v
```

To clean generated files:

```sh
rm -f *.glob *.vo *.vos *.vok *.html *.css
```

## Installing Rocq

Install [Rocq 9.2.0](https://rocq-prover.org/releases/9.2.0) (e.g., via opam).
Rocq 9.3 may also work, but has not been tested with this development.

We recommend RocqIDE or VsCoq to step through the proofs.
