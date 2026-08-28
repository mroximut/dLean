import dLean.Core.Ode

/--
Coordinatewise differentiation for an indexed state space. The base instance
handles `I → F`; the product instance lifts it to finite tuples of such spaces.
-/
class Coordinatewise (I E : Type) where
  deriv : Set I → (ℝ → E) → E → Set ℝ → ℝ → Prop
  mono : ∀ created trajectory rhs t {smaller larger : Set ℝ},
    smaller ⊆ larger →
      deriv created trajectory rhs larger t →
      deriv created trajectory rhs smaller t

instance functionCoordinatewise
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] : Coordinatewise I (I → F) where
  deriv created trajectory rhs interval t :=
    ∀ i ∈ created, HasDerivWithinAt (fun τ => trajectory τ i) (rhs i) interval t
  mono := by grind only [HasDerivWithinAt.mono]

instance productCoordinatewise
    {E₁ E₂ : Type} [Coordinatewise I E₁] [Coordinatewise I E₂] :
    Coordinatewise I (E₁ × E₂) where
  deriv created trajectory rhs interval t :=
    Coordinatewise.deriv created (fun τ => (trajectory τ).1) rhs.1 interval t ∧
      Coordinatewise.deriv created (fun τ => (trajectory τ).2) rhs.2 interval t
  mono := by grind only [Coordinatewise.mono]

instance qode
    [Coordinatewise I E] : Denotable (Set I × (E → E)) E where
  denotation := fun qode : Set I × (E → E) =>
    fun trajectory interval => ∀ t ∈ interval,
      Coordinatewise.deriv qode.1 trajectory (qode.2 (trajectory t)) interval t
  restriction_closed qode := by
    intro trajectory smaller larger hSubset hODE t ht
    exact Coordinatewise.mono (I := I) (E := E) _ _ _ _ hSubset (hODE t (hSubset ht))
