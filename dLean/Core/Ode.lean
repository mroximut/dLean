import dLean.Core.Semantics

/--
A representation of an ODE that can be interpreted as
semantic trajectory constraints.
-/
class Denotable (α : Type u) (σ : outParam (Type v)) where
  denotation : α → SemanticODE σ
  restriction_closed (ode : α) : RestrictionClosed (denotation ode)

instance ode
    [NormedAddCommGroup E] [NormedSpace ℝ E] : Denotable (E → E) E where
  denotation := fun ode : E → E =>
    fun trajectory interval => ∀ t ∈ interval,
      HasDerivWithinAt trajectory (ode (trajectory t)) interval t
  restriction_closed ode := by
    intro trajectory smaller larger hSubset hODE t ht
    exact (hODE t (hSubset ht)).mono hSubset

def evolve [Denotable α σ] (ode : α) (domain : σ → Prop) : HP σ σ :=
  evolveSemantic (Denotable.denotation ode) domain

theorem dC
    [Denotable α σ] {ode : α} {domain pre cut post : σ → Prop}
    (hCut : Ensures (evolve ode domain) pre cut)
    (hPost : Ensures (evolve ode (fun st => domain st ∧ cut st)) pre post) :
    Ensures (evolve ode domain) pre post :=
  SemanticODE.dCut (Denotable.restriction_closed ode) hCut hPost

theorem dW
    [Denotable α σ] {ode : α} {domain pre post : σ → Prop}
    (hDomain : ∀ st, domain st → post st) :
    Ensures (evolve ode domain) pre post :=
  SemanticODE.dWeakening hDomain

theorem dIeq
    [Denotable α σ] {ode : α} {domain pre : σ → Prop}
    (f f' : σ → ℝ)
    (hDerivative : HasDerivative (Denotable.denotation ode) f f')
    (hInitial : ∀ st, pre st → f st = 0)
    (hDerivativeZero : ∀ st, domain st → f' st = 0) :
    Ensures (evolve ode domain) pre (fun st => f st = 0) :=
  SemanticODE.dInvariantEq
    (Denotable.denotation ode)
      domain pre f f' hDerivative hInitial hDerivativeZero

theorem dIle
    [Denotable α σ] {ode : α} {domain pre : σ → Prop}
    (f f' : σ → ℝ)
    (hDerivative : HasDerivative (Denotable.denotation ode) f f')
    (hInitial : ∀ st, pre st → f st ≤ 0)
    (hDerivativeNonpositive : ∀ st, domain st → f' st ≤ 0) :
    Ensures (evolve ode domain) pre (fun st => f st ≤ 0) :=
  SemanticODE.dInvariantLe
    (Denotable.denotation ode)
      domain pre f f' hDerivative hInitial hDerivativeNonpositive

theorem dIlt
    [Denotable α σ] {ode : α} {domain pre : σ → Prop}
    (f f' : σ → ℝ)
    (hDerivative : HasDerivative (Denotable.denotation ode) f f')
    (hInitial : ∀ st, pre st → f st < 0)
    (hDerivativeNonpositive : ∀ st, domain st → f' st ≤ 0) :
    Ensures (evolve ode domain) pre (fun st => f st < 0) :=
  SemanticODE.dInvariantLt
    (Denotable.denotation ode)
      domain pre f f' hDerivative hInitial hDerivativeNonpositive
