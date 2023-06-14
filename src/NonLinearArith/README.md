# Non-Linear Arith Overview

Rust Documentation is currently [here](https://github.com/verus-lang/verus/blob/nonlinear_bitvec_docs/source/docs/non_linear_arithmetic/NonLinear_Singular.md).


## Overview (copied and edited from the dafny ver)

Non-linear math is generally undecidable; hence Dafny (and Z3) rely on heuristics to prove such properties.
While wonderful when they work, these heuristics can lead to unstable?(what does this exactly mean?) proofs.  Hence, in many projects,
it can be helpful to turn off these heuristics (via Dafny's `/noNLarith` flag) and instead explicitly
invoke the lemmas in this library (dafny server --disable-nonlinear-arithmetic for LSP (and let the VSCode plugin work)).  All files in this portion of the library (except those in `Internals/*Nonlinear.dfy`)
verify with the `/noNLarith` flag, which should keep the library itself stable.

In general, it shouldn't be necessary to directly reference anything in `Internals`.
