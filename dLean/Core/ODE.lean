import dLean.Core.Semantics
import Mathlib.Analysis.ODE.Basic

/--
`α` represents a type whose terms can be interpreted as ODEs over
states of type `σ`.

`denotation` interprets a value of type `α` as semantic constraints on
trajectories. `rest_closed` states that these constraints are preserved
when the time interval is restricted.
-/
class Denotable (α : Type u) (σ : outParam (Type v)) where
  denotation : α → SemanticODE σ
  rest_closed (ode : α) : SemanticODE.RestrictionClosed (denotation ode)

/--
Interpret an autonomous vector field `ode : E → E` as the ODE
`trajectory' t = ode (trajectory t)`.
-/
instance ODE
    [NormedAddCommGroup E] [NormedSpace ℝ E] : Denotable (E → E) E where
  denotation := fun ode : E → E =>
    fun trajectory interval => ∀ t ∈ interval,
      HasDerivWithinAt trajectory (ode (trajectory t)) interval t
  rest_closed ode := by
    grind [SemanticODE.RestrictionClosed, HasDerivWithinAt.mono]

/--
Interpret a time-dependent vector field `ode : ℝ → E → E` using mathlib's
`IsIntegralCurveOn` predicate.
-/
instance timeDependentODE
    [NormedAddCommGroup E] [NormedSpace ℝ E] : Denotable (ℝ → E → E) E where
  denotation := fun ode : ℝ → E → E =>
    fun trajectory interval => IsIntegralCurveOn trajectory ode interval
  rest_closed ode := by
    grind only [SemanticODE.RestrictionClosed, IsIntegralCurveOn.mono]

/--
Evolve a state along the trajectories permitted by `ode`, subject to the
evolution-domain constraint `domain`.
-/
def evolve [Denotable α σ] (ode : α) (domain : σ → Prop) : σ → SetM σ :=
  evolveSemantic (Denotable.denotation ode) domain

/--
Differential cut: first establish `cut`, then use it as an additional
evolution-domain assumption when proving `post`.
-/
theorem dC
    [Denotable α σ] {ode : α} {domain pre cut post : σ → Prop}
    (hcut : Ensures (evolve ode domain) pre cut)
    (hpost : Ensures
      (evolve ode (fun st => domain st ∧ cut st)) pre post) :
    Ensures (evolve ode domain) pre post :=
  SemanticODE.dCut (Denotable.rest_closed ode) hcut hpost

/--
Differential weakening: every state satisfying the evolution domain also
satisfies the postcondition.
-/
theorem dW
    [Denotable α σ] {ode : α} {domain pre post : σ → Prop}
    (hdom : ∀ st, domain st → post st) :
    Ensures (evolve ode domain) pre post :=
  SemanticODE.dWeakening hdom

/--
Generic differential invariant rule for a scalar observable `f`.

If the observable initially satisfies `invariantRel (f st) 0` and its derivative
`f'` satisfies `changeRel (f' st) 0` throughout the evolution domain, then we
can conclude that after the evolution we have `invariantRel (f' st) 0`
-/
theorem dI
    [Denotable α σ]
    (invariantRel : ℝ → ℝ → Prop)
    {changeRel : ℝ → ℝ → Prop}
    [rule : DInvariantRelation invariantRel changeRel]
    {ode : α} {domain pre : σ → Prop}
    (f f' : σ → ℝ)
    (hprime : HasPrime (Denotable.denotation ode) f f')
    (hinit : ∀ st, pre st → invariantRel (f st) 0)
    (hchange : ∀ st, domain st → changeRel (f' st) 0) :
    Ensures (evolve ode domain) pre (fun st => invariantRel (f st) 0) :=
  semanticDI (invariantRel := invariantRel) (changeRel := changeRel)
    (Denotable.denotation ode) domain pre f f' hprime hinit hchange

/--
Differential invariant rule for equality. An observable that is initially
zero and has derivative zero remains zero after the evolution.
-/
theorem dIeq
    [Denotable α σ] {ode : α} {domain pre : σ → Prop}
    (f f' : σ → ℝ)
    (hprime : HasPrime (Denotable.denotation ode) f f')
    (hinit : ∀ st, pre st → f st = 0)
    (hprime_zero : ∀ st, domain st → f' st = 0) :
    Ensures (evolve ode domain) pre (fun st => f st = 0) :=
  dI Eq f f' hprime hinit hprime_zero

/--
Differential invariant rule for nonpositive observables. An observable that
is initially nonpositive and has a nonpositive derivative remains nonpositive
after the evolution.
-/
theorem dIle
    [Denotable α σ] {ode : α} {domain pre : σ → Prop}
    (f f' : σ → ℝ)
    (hprime : HasPrime (Denotable.denotation ode) f f')
    (hinit : ∀ st, pre st → f st ≤ 0)
    (hprime_le : ∀ st, domain st → f' st ≤ 0) :
    Ensures (evolve ode domain) pre (fun st => f st ≤ 0) :=
  dI (· ≤ ·) f f' hprime hinit hprime_le

/--
Differential invariant rule for strictly negative observables. An observable
that is initially negative and has a nonpositive derivative remains negative
after the evolution.
-/
theorem dIlt
    [Denotable α σ] {ode : α} {domain pre : σ → Prop}
    (f f' : σ → ℝ)
    (hprime : HasPrime (Denotable.denotation ode) f f')
    (hinit : ∀ st, pre st → f st < 0)
    (hprime_le : ∀ st, domain st → f' st ≤ 0) :
    Ensures (evolve ode domain) pre (fun st => f st < 0) :=
  dI (· < ·) f f' hprime hinit hprime_le

/--
Differential invariant rule for nonnegative observables. An observable that
is initially nonnegative and has a nonnegative derivative remains nonnegative
after the evolution.
-/
theorem dIge
    [Denotable α σ] {ode : α} {domain pre : σ → Prop}
    (f f' : σ → ℝ)
    (hprime : HasPrime (Denotable.denotation ode) f f')
    (hinit : ∀ st, pre st → f st ≥ 0)
    (hprime_ge : ∀ st, domain st → f' st ≥ 0) :
    Ensures (evolve ode domain) pre (fun st => f st ≥ 0) :=
  dI (· ≥ ·) f f' hprime hinit hprime_ge

/--
Differential invariant rule for strictly positive observables. An observable
that is initially positive and has a nonnegative derivative remains positive
after the evolution.
-/
theorem dIgt
    [Denotable α σ] {ode : α} {domain pre : σ → Prop}
    (f f' : σ → ℝ)
    (hprime : HasPrime (Denotable.denotation ode) f f')
    (hinit : ∀ st, pre st → f st > 0)
    (hprime_ge : ∀ st, domain st → f' st ≥ 0) :
    Ensures (evolve ode domain) pre (fun st => f st > 0) :=
  dI (· > ·) f f' hprime hinit hprime_ge
