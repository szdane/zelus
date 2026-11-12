The scalar `T-DER-FIN` implementation follows Figure 5 and Definition 5 of
*Towards Formal Verification of Hybrid Synchronous Programs* (NFM manuscript).

Give the safety property on the derivative's variable and give a differential
invariant on the initializer and every reset expression:

```ocaml
let hybrid sawtooth () = x where
  rec der (x : {v:float | globally (0.0 <= v && v <= 1.0)}) = 1.0
    init (0.0 : {v:float | globally (0.0 <= v)})
    reset up (x -. 1.0) -> (0.0 : {v:float | globally (0.0 <= v)})
```

For each segment the verifier checks:

1. The entry value satisfies both safety and its supplied invariant.
2. The active-guard domain implies the dL derivative of that invariant, after
   substituting the ODE's right-hand side for the state's derivative.
3. The invariant and the active-guard domain imply safety.

A reset is checked under pre-reset safety and equality of its guard to zero.
The pre-reset state, segment entry and arbitrary continuous state are distinct
solver variables. Only verified safety is exported to the enclosing body (T3).
Neither safety nor the proposed invariant at the continuous state is assumed
while proving the differential premise.

Activity is evaluated at segment entry: `u < 0 || (u = 0 && du < 0)`. At zero,
the guard must move into its negative region. This follows the manuscript's
prose; the implication printed inside Definition 5 is treated as a typo.
Activity remains a symbolic condition, so an uncertain guard is never assumed
active. The supplied invariant is explicitly established at entry as required
by the preservation proof.

This first version supports one scalar float derivative per function, polynomial
ODEs/guards and arithmetic initializer/reset expressions. `last x` in a reset
denotes the pre-reset state. A separate `init x = ...` is also supported.
Verified numeric global constants may occur in the predicates and expressions;
other local variables, calls and stateful reset programs are rejected in this
version. Invariants are supplied by the user, never inferred. They may differ
between initialization and individual reset branches. An optional outer
`globally` is accepted; discrete temporal operators are not.

Run the example (requires `fixpoint` on PATH):

```sh
dune build compiler/zeluc.exe lib/std/stdlib.zci
compiler/zeluc.exe -stdlib _build/default/lib/std -verify \
  verification_examples/hybrid/derivative_rule.zls
```

Run the compiler/solver regression tests with `dune exec test/hybrid_typing.exe`.
Failures identify the premise, such as `T1-flow` or `T2-1-bridge`, and save the
Fixpoint query using the existing failure-dump mechanism.
