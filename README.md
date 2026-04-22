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
