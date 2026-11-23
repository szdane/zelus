The `T-DER-FIN` implementation follows the revised rule based on Figure 5 and Definition 5 of
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
   substituting the ODE's right-hand side for the state's derivative. Top-level
   conjunctions are checked left to right as differential cuts: a conjunct's
   flow-state fact becomes available only after its own preservation succeeds.
3. The invariant and the active-guard domain imply safety.

A reset is checked under pre-reset safety, equality of its guard to zero, and
necessary upward-crossing direction facts described below.
The pre-reset state, segment entry and arbitrary continuous state are distinct
solver variables. Only verified safety is exported to the enclosing body (T3).
Neither safety nor the proposed invariant at the continuous state is assumed
while proving the differential premise.

For a coupled vector field, annotate the tuple of continuous variables with a
labeled-tuple refinement. The initializer and every reset carry a refinement
with the same number of scalar float fields; their binder names may differ:

```ocaml
let hybrid oscillator () = (position, velocity) where
  rec der ((position, velocity) : {(p:float) * (q:float) |
    globally (p *. p +. q *. q <= 1.0)}) = (velocity, -. position)
    init ((1.0, 0.0) : {(p0:float) * (q0:float) |
      p0 *. p0 +. q0 *. q0 <= 1.0})
```

The verifier differentiates the shared invariant using the complete vector
field, so the two terms in the energy derivative cancel. It creates a fresh
scalar ghost for **each component** of each pre-reset, segment-entry and flow
vector. Reset assignments read the same pre-reset vector simultaneously.
`last position` in a tuple reset reads that vector's position component.
Guard activation evaluates the full Lie derivative at the entry vector, while
the resulting domain facts constrain only the flow vector. After all checks
pass, the joint safety predicate is available through the component variables
for checking subsequent equations and scalar or tuple returns. Entry values
and auxiliary invariants are not exported as standing facts.

`watertank_vector.zls` is an executable two-state example with `level' = rate`,
`rate' = 0` and boundary resets that reverse the rate. Both level bounds are
supplied by active guards, so its auxiliary invariants can be `true`.

The other executable examples follow the paper:

- `bouncing_ball.zls` (Appendix E.3) releases the ball from height 10 under
  gravity 9.81 and resets velocity to `-0.8 * last velocity` at ground impact.
  The certificate is the energy bound `2*g*height + velocity^2 <= 2*g*10`;
  the active ground detector supplies `height >= 0`. The verified return
  property is `0 <= height <= 10`.
- `cruise_control.zls` (Sections 5.2/E.2) is the paper's **event-triggered
  automatic braking** example with a stationary obstacle at position 5, brake
  acceleration -0.2 and safety margin 0.1. Its stopping-position expression
  `position + 2.5*speed^2` is algebraically identical to the paper's
  `position - speed^2/(2*brake)` for that fixed brake value. This polynomial
  spelling fits the verifier's arithmetic fragment. Acceleration and then
  stopped velocity are proved as differential cuts before the stopping bound.
  The verified return property is `position < 5`.

At a reset triggered by `up(u)`, let `du` and `ddu` be the first and second Lie
derivatives of the guard under the pre-reset vector field. The verifier also
uses `du > 0 || (du = 0 && ddu = 0)`. This is a necessary condition for an
upward crossing of the supported smooth polynomial guards: when `du = 0`, a
nonzero quadratic term cannot change sign across the root; a zero plateau
has both derivatives zero at its endpoint. These are pre-reset facts only.
In particular, the ground guard's `ddu = gravity > 0` establishes strictly
downward incoming velocity, hence upward post-bounce velocity. Cubic crossings
with `du = ddu = 0` remain possible; the checker does not assume transversality.

Differential cuts never assume the conjunct currently being checked or a later
conjunct. Their entry conditions are all proved first. This supports the
cruise-control certificates without assuming the safety property at the
arbitrary flow state. The conjunction order in those annotations is significant.

Activity is evaluated at segment entry: `u < 0 || (u = 0 && du < 0)`. At zero,
the guard must move into its negative region. This follows the manuscript's
prose; the implication printed inside Definition 5 is treated as a typo.
Activity remains a symbolic condition, so an uncertain guard is never assumed
active. The supplied invariant is explicitly established at entry as required
by the preservation proof.

This version supports one annotated derivative group per function: either a
scalar float or a flat tuple of floats of any arity. Coupled states must be
combined in that tuple; separately declared derivative equations are rejected.
ODEs and guards must be polynomial, and initializer/reset values must be
arithmetic expressions (tuple literals for a tuple state). General calls,
nested product states and stateful reset programs are not supported by the
verifier. `last x` in a reset denotes the pre-reset state. A separate
`init x = ...` is also supported for named derivatives.
Verified numeric global constants may occur in the predicates and expressions;
other local variables are rejected in the vector field. Invariants are supplied
by the user, never inferred. They may differ
between initialization and individual reset branches. An optional outer
`globally` is accepted; discrete temporal operators are not.

Run the example (requires `fixpoint` on PATH):

```sh
dune build compiler/zeluc.exe lib/std/stdlib.zci
compiler/zeluc.exe -stdlib _build/default/lib/std -verify \
  verification_examples/hybrid/watertank_vector.zls
```

Run the compiler/solver regression tests with `dune exec test/hybrid_typing.exe`.
The suite reads the bouncing-ball and cruise-control sources directly so their
proofs cannot drift from the runnable examples. Build either executable with
`make bouncing_ball` or `make cruise_control` in this directory, using a rebuilt
compiler on `PATH` (or overriding `ZELUC`).
Failures identify the premise, such as `T1-flow` or `T2-1-bridge`, and save the
Fixpoint query using the existing failure-dump mechanism.
