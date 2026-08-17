# VNNLIB-Rocq

This repository is a Rocq translation of [VNNLIB-Agda](https://github.com/VNNLIB/VNNLIB-Agda),
the official Agda library for interacting with the [VNN-LIB standard](https://www.vnnlib.org/).
It ports the Agda formalisation of the standard's syntax and semantics onto the
[Mathematical Components](https://math-comp.github.io/) library, in place of the Agda
standard library.

It includes:
- `ONNX.Syntax`: abstract interface for the syntax of ONNX
- `ONNX.Semantics`: abstract interface for the semantics of ONNX
- `VNNLIB.Syntax`: intrinsically-typed syntax for VNNLIB queries
- `VNNLIB.Semantics`: semantics for VNNLIB queries

The following modules exist in VNNLIB-Agda but have not yet been ported:
- `ONNX.Parser`: very minimal abstract interface for parsing ONNX constants
- `VNNLIB.Parser`: ability to parse/type-check a string into VNNLIB queries
- `VNNLIB.Theories`: orthogonal subsets of the query syntax
- `VNNLIB.Logics`: overall subsets of the query syntax
- `VNNLIB.Solver`: an interface for solvers of VNNLIB queries
- `VNNLIB.Example`: some simple examples of how to use the library

## Known short-comings

* Does not yet cover all the logics and theories in VNNLIB 2.0.
* No parser: queries currently have to be built directly as Rocq terms.

## Version compatibility

| VNNLIB-Rocq version | VNNLIB-Agda version | VNNLIB version |
| --- | --- | --- |
| unreleased | v1.0.0 - v1.1.1 | v2.0 |

## Requirements

- [Rocq](https://rocq-prover.org/) 9.1.1
- [Hierarchy Builder](https://github.com/math-comp/hierarchy-builder)
- [Mathematical Components](https://github.com/math-comp/math-comp) >= 2.6.0
- [Mathematical Components Analysis](https://github.com/math-comp/analysis)

Later versions of these tools may work but are not tested.

## Setup

1. Install Rocq and the required Mathematical Components packages (e.g. via opam).

2. Clone this repository and navigate into it:
   ```bash
   git clone https://github.com/lstrsrmn/VNNLIB-Rocq.git
   cd VNNLIB-Rocq
   ```

3. Build the project:
   ```bash
   make
   ```
   This generates `Makefile.coq` from `_CoqProject` via `rocq makefile` and builds
   `ONNX/Syntax.v`, `ONNX/Semantics.v`, `VNNLIB/Syntax.v` and `VNNLIB/Semantics.v`.

## Getting started with the library

There is not yet an `Examples` file (see [Known short-comings](#known-short-comings)).
In the meantime, `VNNLIB/Semantics.v` is the best starting point: it shows how the
syntax defined in `VNNLIB/Syntax.v` and `ONNX/Syntax.v` is given meaning in terms of
the tensor semantics from `ONNX/Semantics.v`.
