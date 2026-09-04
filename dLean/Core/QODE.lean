import dLean.Core.ODE

/-!
# QODE

This module defines quantified ordinary differential equations, i.e. ODEs over
function-valued states. A quantified ODE consists of a set of active indices
together with a vector field, e.g. `Set I × ((I → ℝ) → (I → ℝ))`, where `I`
is the index type. If, e.g. `x : I → ℝ` denotes the position for every car
and `v : I → ℝ` their velocity, then the vector field would send `x` to `v`,
corresponding to the fact that for all active indices `i` `x(i)` has the time
derivative `v(i)`. During an evolution, the differential equation constrains
every active coordinate simultaneously; coordinates outside the active set
remain unconstrained.

The `QODE` instance interprets a pair `Set I × (F → F)` as a `Denotable` ODE.
Quantified ODEs can therefore use the same `evolve` operator and differential
proof rules as the ordinary ODEs defined in `dLean.Core.ODE`.
-/

namespace dLean

/--
An indexed derivative relation for `F`-valued trajectories.

`Derivable.has_deriv indices trajectory rhs interval t` states that
`trajectory` has derivative `rhs` at time `t`, on `interval`, at the selected
indices. The `mono` field makes this relation stable under restricting the
time interval.

The purpose of this is to introduce the notion of time-derivation for
especially function-valued states that are not already covered by mathlib's
`HasDerivWithinAt`.
-/
class Derivable (I F : Type) where
  has_deriv
    (indices : Set I) (trajectory : ℝ → F) (rhs : F)
    (interval : Set ℝ) (timePoint : ℝ) : Prop
  mono : ∀ indices trajectory rhs t {smaller larger : Set ℝ},
    smaller ⊆ larger →
      has_deriv indices trajectory rhs larger t →
      has_deriv indices trajectory rhs smaller t

/--
Coordinatewise differentiation for function-valued states `I → E`.

A function-valued state `f : I → E` has the time-derivative `f' : I → E` at a
time point `t` (on an index set `indices : Set I`) if for every index
`i ∈ indices`, f(i) has the time-derivative f'(i) at `t`.
-/
instance functionCoordinatewise
    [NormedAddCommGroup E] [NormedSpace ℝ E] : Derivable I (I → E) where
  has_deriv indices trajectory rhs interval t :=
    ∀ i ∈ indices, HasDerivWithinAt (fun t => trajectory t i) (rhs i) interval t
  mono := by grind only [HasDerivWithinAt.mono]

/--
Coordinatewise differentiation for product states, obtained by differentiating
both components coordinatewise.
-/
instance productCoordinatewise
    [Derivable I F₁] [Derivable I F₂] : Derivable I (F₁ × F₂) where
  has_deriv indices trajectory rhs interval t :=
    Derivable.has_deriv indices (fun t => (trajectory t).1) rhs.1 interval t ∧
      Derivable.has_deriv indices (fun t => (trajectory t).2) rhs.2 interval t
  mono := by grind only [Derivable.mono]

/--
A quantified ODE is an "active" set of indices together with a vector
field on a state type that supports coordinatewise differentiation.
-/
instance QODE
    [Derivable I F] : Denotable (Set I × (F → F)) F where
  denotation := fun qode : Set I × (F → F) =>
    fun trajectory interval => ∀ t ∈ interval,
      Derivable.has_deriv qode.1 trajectory (qode.2 (trajectory t)) interval t
  rest_closed qode := by grind [Derivable.mono, SemanticODE.RestrictionClosed]

end dLean
