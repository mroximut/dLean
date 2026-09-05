---
name: dlean-prover
description: Prove and maintain dLean hybrid-program theorems using SetM weakest preconditions, mvcgen loop invariants, differential cuts and invariants, and ODE or QODE derivative tactics. Use for proof work in the dLean library and its clients, not for general Lean theorem proving.
---

# dLean Prover

Prove or maintain the requested theorem in the style supported by the active dLean checkout. This
skill supplements general Lean skills with dLean-specific semantics, proof rules, and `mvcgen`
patterns.

Before proving, inspect the relevant modules under `dLean/Core` and `dLean/Tactic`; they are the
authoritative APIs. Inspect nearby dLean examples when they are available, especially when the task
asks for the project's established proof style. Do not carry API assumptions across dLean
checkouts.

## Read the program as demonic nondeterminism

`SetM` represents all possible results of a computation. Safety therefore means that the
postcondition holds for every member of `SetM.run`.

When a theorem is stated using membership in `SetM.run`, use the existing WP bridge rather than
unfolding the set monad:

```lean
intro ... result hrun
apply SetM.of_wp_run_mem hrun
unfold prog
mvcgen
```

The target is now a weakest-precondition obligation. Avoid globally unfolding `SetM`, its monad
instances, or `SetM.run`: doing so loses the abstraction on which `mvcgen` and the registered specs
operate.

The library already registers `[spec]` rules for:

- `choose`: prove the continuation for every chosen value;
- `chooseS`: prove it for every member of the chosen set;
- `abort`: no successful result exists;
- `test`: assume the tested proposition;
- `evolveSemantic`, hence `evolve`: prove the continuation for every permitted evolution.

These theorems are normally used implicitly by `mvcgen`; their absence from the proof script is
expected. Ordinary mutable bindings and assignments do not need custom specs.

## Build the mathematical invariant before running the loop proof

Identify a predicate strong enough both to survive one iteration and to imply the final safety
claim. Define it as a named `@[simp] def` when controlled unfolding will help arithmetic and
structural simplification.

Typical invariant designs in this library are:

- an energy or barrier inequality plus evolution-domain facts for scalar hybrid systems;
- a positive-slack separating margin, with its geometric witnesses stored existentially, for
  vector systems;
- pairwise ordering of every active pair for quantified systems.

First prove focused helper theorems for the continuous commands. Keep `mvcgen` for imperative
composition and use dLean's differential rules for evolution. This separates program VCs from the
mathematics of the invariant.

## State the `mvcgen` loop invariant with the generated state shape

After the initial `mvcgen`, introduce the parameters it exposes, then invoke the invariant form:

```lean
unfold prog
mvcgen
intros
mvcgen invariants
| inv1 => ⇓⟨xs, state⟩ => ⌜invariant parameters state⌝
```

Match `state` to all mutable locals, in declaration order. Examples of generated shapes are:

```lean
| inv1 => ⇓⟨xs, (x, v)⟩ => ⌜invariant g H (x, v)⌝
| inv1 => ⇓⟨xs, (created, x, v, a)⟩ => ⌜invariant created x v a⌝
```

`xs` is `mvcgen`'s remaining loop-enumeration state; retain it in the pattern even when the
mathematical invariant does not mention it. Destructured `let mut` bindings are threaded as tuples,
and several mutable declarations produce a nested product visible in the generated goal.

Do not guess verification-condition numbers from another theorem. Compile after declaring the
invariant and use the case names Lean reports. Common obligations are:

- `step` or `step.isTrue` / `step.isFalse`: preservation by one loop body or conditional branch;
- `vc1.pre`: the initial state establishes the invariant;
- `post` or `post.success`: the invariant implies the returned safety property.

Inside a loop body, another `mvcgen` may be needed to expose an inner `choose`, `chooseS`, `unless`,
or evolution. A common preservation branch is:

```lean
case vc1.step =>
  intros
  mvcgen
  simp only [WP.pure]
  apply continuous_preserves
  -- establish the helper's precondition from the loop invariant and branch facts
```

The exact case name and required `intros` depend on the program. Follow the live goal instead of
depending on generated binder names.

## Prove evolution preservation with dLean rules

Evolution statements use `Ensures` notation:

```lean
pre [[evolve ode domain]] post
```

Use the rules according to the mathematical argument:

- `dW`: derive the postcondition directly from the evolution domain;
- `dC (cut := cutPredicate)`: establish a fact along the evolution, then add it to the domain for
  the remaining proof;
- `dIeq`, `dIle`, `dIlt`, `dIge`, `dIgt`: preserve respectively equality, nonpositive, negative,
  nonnegative, or positive scalar observables;
- `Ensures.nondet_choice`: prove both sides of `p ∪ q`;
- `Ensures.iff_run`: switch to explicit initial/final states when lifting a pointwise preservation
  theorem through a quantified invariant.

A standard differential-cut proof is:

```lean
apply dC (cut := fun st => observable st ≤ 0)
· apply dIle observable
  · autodiff
  · -- the precondition initially implies observable <= 0
  · -- the domain implies the Lie derivative <= 0
· apply dW
  -- rebuild the desired invariant from the strengthened domain
```

Nested cuts are intentional when one differential invariant depends on another. For example,
quantified ordering is naturally proved by preserving acceleration gap `<= 0`, then velocity gap
`<= 0`, then position gap `< 0`, followed by `dW` to reassemble the ordering predicate.

For a nondeterministic continuous command, prove each ODE once and compose them:

```lean
apply Ensures.nondet_choice
· exact left_evolution_preserves ...
· exact right_evolution_preserves ...
```

When the invariant quantifies over indices or contains a disjunction, it can be clearer to use
`(Ensures.iff_run _ _ _).mpr`, introduce the final state and evolution-membership hypothesis, and
apply the pointwise preservation theorem in each branch.

## Choose the derivative tactic that matches the ODE representation

For ordinary autonomous vector fields:

- `autodiff` computes the scalar Lie derivative and proves the `HasPrime` goal;
- `autodiff` supports `+`, `-`, multiplication, scalar multiplication, inner products, negation,
  literal natural powers, `Real.sin`, and `Real.cos`;
- if the derivative function is supplied explicitly, use `ode_deriv` or let `autodiff` delegate to
  it;
- pass extra unfolding lemmas as `ode_deriv [definitions]` when inference does not normalize an
  observable or vector field.

For quantified ODEs represented by `Set I × (F → F)`:

- use `qode_deriv` on `HasPrime` goals;
- provide the named gap, projection, and motion definitions needed for simplification, for example
  `qode_deriv [vGap', motion]`;
- the tactic obtains coordinate derivatives only for active indices, so retain and supply index
  membership facts such as `i ∈ created` and `j ∈ created`.

Both derivative tactics unfold the ODE, domain, observable, and proposed derivative automatically.
Add explicit definitions only when the current goal shows that further unfolding is required.

## Finish VCs in the local proof style

- Use `simp only [WP.pure]` when a generated VC still contains a nested pure WP before applying an
  `Ensures` helper.
- Use `simp`, `simp_all`, or `grind [definitions]` to expose tuple projections, domains, record-free
  state updates, and invariant structure.
- Name non-obvious arithmetic or geometric facts with `have` before calling `linarith` or
  `nlinarith`. Typical facts include `sq_nonneg v`, the sign of an odd power, `c ^ 2 ≤ 1`, and
  `-1 ≤ ⟨u, d⟩` for unit vectors.
- Destruct existential invariant witnesses explicitly with `rcases`; automation will not invent or
  extract the separating direction and positive slack.
- In the final postcondition VC, unpack only the invariant information needed to show the returned
  value is safe.

When the requested style is `mvcgen`, do not replace this architecture with a large direct proof
over set membership merely because it can be unfolded. The library examples use direct run
reasoning as a localized bridge, such as `Ensures.iff_run`, while program composition remains in
WP/`mvcgen` form.

## Diagnose by layer

- If `mvcgen` stops at a primitive, inspect its `[spec]` theorem in `dLean/Core/Semantics.lean` and
  ensure the primitive has not been hidden behind an opaque local definition.
- If a loop invariant pattern does not elaborate, inspect the generated product state after the
  first `mvcgen`; include every mutable local and the leading `xs` component.
- If `apply` fails after `mvcgen`, first normalize (`simp [WP.pure]`); then compare the helper theorem's
  `Ensures` precondition with the current invariant.
- If `autodiff` reports an unsupported expression or ODE, provide an explicit derivative and use
  `ode_deriv`, or prove `HasPrime` from the semantic derivative assumptions.
- If `qode_deriv` cannot find a coordinate derivative, check both that the state is built from
  supported function/product `Derivable` instances and that the coordinate is in the active set.
- If arithmetic automation stalls, simplify the named observable and derivative, normalize with
  `ring_nf`, then state the missing sign fact explicitly.

## Final checks

1. Run `lake env lean path/to/EditedFile.lean` from the project root.

