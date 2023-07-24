# Non-Linear Arith Overview

Rust Documentation is currently [here](https://github.com/verus-lang/verus/blob/nonlinear_bitvec_docs/source/docs/non_linear_arithmetic/NonLinear_Singular.md).


# Overview 

(copied and edited from the dafny ver)

Non-linear math is generally undecidable; hence Z3 rely on heuristics to prove such properties.
While wonderful when they work, these heuristics can lead to unstable proofs.  Hence, in many projects,
it can be helpful to turn off these heuristics (and verus turns nl off in the first place, you can see `(set-option :smt.arith.nl false)` in the smt log file) and instead explicitly
invoke the lemmas in this library. All files in this portion of the library (except those in `Internals/*Nonlinear.rs`)
verify without Non-Linear arithmetic reasoning, which should keep the library itself stable.

In general, it shouldn't be necessary to directly reference anything in `Internals`.

For better stability results, every proof funcitons currently have `verfier::spinoff_prover` attribute to prevent context pollution. However, this causes huge smt overhead for initializing the queries.