import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import dLean.Core.SetMWP
open Std.Do

/-!
A hybrid program is represented as a function that returns SetM α.
-/

instance {σ α : Type u} : Union (σ → SetM α) where
  union p q st := p st <|> q st

def abort : SetM α := fun _ => False

def choose (α : Type u) : SetM α := Set.univ

def chooseS (S : SetM α) : SetM α := S

def test (P : Prop) : SetM Unit := fun _ => P

abbrev Box (prog : σ → SetM α) (post : α → Prop) : σ → Prop :=
  fun st => (wp⟦prog st⟧ (⇓ res => ⌜post res⌝)).down

notation:25 "[["p"]] " post => Box p post

abbrev Ensures
    (prog : σ → SetM α) (pre : σ → Prop) (post : α → Prop) : Prop :=
  ∀ st, pre st → (Box prog post) st

notation:25 pre " [["p"]] " post => Ensures p pre post

theorem Box.iff_run (prog : σ → SetM α) (post : α → Prop) (st : σ) :
  (Box prog post) st ↔ (∀ st', st' ∈ SetM.run (prog st) → post st') := by rfl

namespace Ensures

theorem iff_run (p : σ → SetM α) (pre : σ → Prop) (post : α → Prop) :
  Ensures p pre post ↔
    ∀ st, pre st → ∀ st', st' ∈ SetM.run (p st) → post st' := by rfl

theorem iff_triple (p : σ → SetM α) (pre : σ → Prop) (post : α → Prop) :
  Ensures p pre post ↔ ∀ st, ⦃⌜pre st⌝⦄ p st ⦃⇓ st' => ⌜post st'⌝⦄ := by rfl

theorem nondet_choice
    {p q : σ → SetM α} {pre : σ → Prop} {post : α → Prop}
    (hleft : Ensures p pre post) (hright : Ensures q pre post) :
    Ensures (p ∪ q) pre post := by
  intro st hpre
  exact SetM.wp_orElse _ _ (hleft st hpre) (hright st hpre)

end Ensures

@[spec]
theorem choose_spec {Q : PostCond α .pure} :
    ⦃⌜∀ n, (Q.1 n).down⌝⦄ choose α ⦃Q⦄ := by
  apply Triple.iff.mpr
  intro h n hn
  exact h n

@[spec]
theorem chooseS_spec {Q : PostCond α .pure} :
    ⦃⌜∀ n ∈ SetM.run S, (Q.1 n).down⌝⦄ chooseS S ⦃Q⦄ := by
  apply Triple.iff.mpr
  intro h n hn
  exact h n hn

@[spec]
theorem abort_spec {Q : PostCond α .pure} :
    ⦃⌜True⌝⦄ abort ⦃Q⦄ := by
  apply Triple.iff.mpr
  intro _ res hres
  exact False.elim hres

@[spec]
theorem test_spec {P : Prop} {Q : PostCond Unit .pure} :
    ⦃⌜P → (Q.1 ()).down⌝⦄ test P ⦃Q⦄ := by
  apply Triple.iff.mpr
  intro h res hres
  exact h hres

/--
Specifies whether a trajectory, i.e a mapping from
time points to states, follows the system throughout an interval.
-/
abbrev SemanticODE (σ : Type u) :=
  (trajectory : ℝ → σ) → (interval : Set ℝ) → Prop

/--
Whether a trajectory satisfies an inital value problem
-/
def IsEvolution
    (trajectory : ℝ → σ) (ode : SemanticODE σ) (domain : σ → Prop)
    (inital : σ) (duration : ℝ) : Prop :=
  trajectory 0 = inital ∧
    (∀ t ∈ Set.Icc 0 duration, domain (trajectory t)) ∧
      ode trajectory (Set.Icc 0 duration)

/--
Interpret a semantic ODE as a hybrid program
-/
def evolveSemantic
    (ode : SemanticODE σ) (domain : σ → Prop) : σ → SetM σ := fun st => do
  let duration ← {duration : ℝ | 0 ≤ duration}
  let trajectory ← {
    trajectory : ℝ → σ | IsEvolution trajectory ode domain st duration
  }
  return trajectory duration

@[spec]
theorem evolveSemantic_spec
    (ode : SemanticODE σ) (domain : σ → Prop) (initial : σ)
    {Q : PostCond σ .pure} :
      ⦃⌜∀ duration : ℝ, 0 ≤ duration →
        ∀ trajectory : ℝ → σ, IsEvolution trajectory ode domain initial duration →
        (Q.1 (trajectory duration)).down⌝⦄
        evolveSemantic ode domain initial ⦃Q⦄ := by
  apply Triple.iff.mpr
  intro h
  unfold evolveSemantic
  intro final hfinal
  change final ∈
    ⋃ duration ∈ {duration : ℝ | 0 ≤ duration},
      ⋃ trajectory ∈ {trajectory : ℝ → σ |
        IsEvolution trajectory ode domain initial duration},
        {trajectory duration} at hfinal
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_singleton_iff] at hfinal
  rcases hfinal with ⟨duration, hduration, trajectory, htrajectory, rfl⟩
  exact h duration hduration trajectory htrajectory

/-- `f'` is the derivative of `f` along every trajectory of an ODE. -/
def HasPrime
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ode : SemanticODE σ) (f f' : σ → E) : Prop :=
  ∀ trajectory interval, ode trajectory interval →
    ∀ t ∈ interval,
      HasDerivWithinAt
      (fun t => f (trajectory t)) (f' (trajectory t)) interval t

namespace SemanticODE

/-- An ODE semantics is closed under restricting its time interval. -/
def RestrictionClosed (ode : SemanticODE σ) : Prop :=
  ∀ (trajectory : ℝ → σ) {smaller larger : Set ℝ}, smaller ⊆ larger →
    ode trajectory larger → ode trajectory smaller

/--
An ODE preserves a state relation between the initial state and
every trajectory point.
-/
def PreservesAgreement
    (ode : SemanticODE σ) (agrees : σ → σ → Prop) : Prop :=
  ∀ trajectory interval, ode trajectory interval →
    ∀ t ∈ interval, agrees (trajectory 0) (trajectory t)

/-- Build membership in a semantic evolution from an explicit trajectory witness. -/
theorem mem_evolveSemantic
    (ode : SemanticODE σ) (domain : σ → Prop)
    (initialState : σ) (duration : ℝ) (trajectory : ℝ → σ)
    (hduration : 0 ≤ duration)
    (hEvolution : IsEvolution trajectory ode domain initialState duration) :
    trajectory duration ∈ SetM.run (evolveSemantic ode domain initialState) := by
  unfold evolveSemantic
  change trajectory duration ∈
    ⋃ d ∈ {d : ℝ | 0 ≤ d},
      ⋃ path ∈ {path : ℝ → σ |
        IsEvolution path ode domain initialState d},
        {path d}
  simp only [Set.mem_iUnion, Set.mem_singleton_iff]
  exact ⟨duration, hduration, trajectory, hEvolution, rfl⟩

/-- Every endpoint of a semantic evolution satisfies its domain constraint. -/
theorem evolveSemantic_domain_at_end
    (ode : SemanticODE σ) (domain : σ → Prop) {initial final : σ}
    (hEvolution : final ∈ SetM.run (evolveSemantic ode domain initial)) :
    domain final := by
  unfold evolveSemantic at hEvolution
  change final ∈
    ⋃ duration ∈ {duration : ℝ | 0 ≤ duration},
      ⋃ trajectory ∈ {trajectory : ℝ → σ |
        IsEvolution trajectory ode domain initial duration},
        {trajectory duration} at hEvolution
  simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hEvolution
  rcases hEvolution with ⟨duration, hDuration, trajectory, hTrajectory, rfl⟩
  exact hTrajectory.2.1 duration ⟨hDuration, le_rfl⟩

/-- Semantic differential weakening: endpoints satisfy consequences of the domain. -/
theorem dWeakening
    {ode : SemanticODE σ} {domain pre post : σ → Prop}
    (hDomain : ∀ st, domain st → post st) :
    Ensures (evolveSemantic ode domain) pre post := by
  intro initial _ final hEvolution
  exact hDomain final (evolveSemantic_domain_at_end ode domain hEvolution)

/-- Predicates depending only on coordinates preserved by an ODE remain true. -/
theorem dFixed
    {ode : SemanticODE σ} {agrees : σ → σ → Prop}
    {domain pre post : σ → Prop}
    (hAgreement : PreservesAgreement ode agrees)
    (hFixed : ∀ initial final, agrees initial final → post initial → post final)
    (hInitial : ∀ st, pre st → post st) :
    Ensures (evolveSemantic ode domain) pre post := by
  intro initial hPre
  refine Triple.iff.mp (evolveSemantic_spec
    (Q := PostCond.noThrow fun final => ⌜post final⌝) ode domain initial) ?_
  intro duration hDuration trajectory hEvolution
  apply hFixed initial (trajectory duration)
  · simpa [hEvolution.1] using
      hAgreement trajectory (Set.Icc 0 duration) hEvolution.2.2 duration
        ⟨hDuration, le_rfl⟩
  · exact hInitial initial hPre

/-- Semantic differential cut, for ODE semantics closed under interval restriction. -/
theorem dCut
    {ode : SemanticODE σ} {domain pre cut post : σ → Prop}
    (hClosed : RestrictionClosed ode)
    (hCut : Ensures (evolveSemantic ode domain) pre cut)
    (hPost : Ensures
      (evolveSemantic ode (fun st => domain st ∧ cut st)) pre post) :
    Ensures (evolveSemantic ode domain) pre post := by
  intro initial hPre
  refine Triple.iff.mp (evolveSemantic_spec
    (Q := PostCond.noThrow fun final => ⌜post final⌝) ode domain initial) ?_
  intro duration hDuration trajectory hEvolution
  have hCutAlong : ∀ t ∈ Set.Icc (0 : ℝ) duration, cut (trajectory t) := by
    intro t ht
    have hSubset : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) duration := by
      intro u hu
      exact ⟨hu.1, hu.2.trans ht.2⟩
    have hPrefix : IsEvolution trajectory ode domain initial t := by
      exact ⟨hEvolution.1,
        fun u hu => hEvolution.2.1 u (hSubset hu),
        hClosed trajectory hSubset hEvolution.2.2⟩
    exact hCut initial hPre (trajectory t)
      (mem_evolveSemantic ode domain initial t trajectory ht.1 hPrefix)
  have hEvolutionCut :
      IsEvolution trajectory ode (fun st => domain st ∧ cut st)
        initial duration := by
    refine ⟨hEvolution.1, ?_, hEvolution.2.2⟩
    intro t ht
    exact ⟨hEvolution.2.1 t ht, hCutAlong t ht⟩
  exact hPost initial hPre (trajectory duration)
    (mem_evolveSemantic ode (fun st => domain st ∧ cut st)
      initial duration trajectory hDuration hEvolutionCut)

/--
Relation R is preserved by the derivative
For R = Eq, f'(t) = 0 → f(end) = f(0)
-/
def PreservedByDerivative (R : ℝ → ℝ → Prop) : Prop :=
  ∀ (duration : ℝ), 0 ≤ duration →
    ∀ (f f' : ℝ → ℝ), (∀ t ∈ (Set.Icc 0 duration),
      HasDerivWithinAt f (f' t) (Set.Icc 0 duration) t) →
        (∀ t ∈ Set.Icc 0 duration, R (f' t) 0) → R (f duration) (f 0)

theorem preservedByDerivative_eq : PreservedByDerivative Eq := by
  intro duration hduration f f' hDerivative hZero
  let interval := Set.Icc (0 : ℝ) duration
  have hDerivativeZero :
      ∀ t ∈ interval, HasDerivWithinAt f 0 interval t := by
    intro t ht
    exact (hDerivative t ht).congr_deriv (hZero t ht)
  have hDifferentiable : DifferentiableOn ℝ f interval := by
    intro t ht
    exact (hDerivativeZero t ht).differentiableWithinAt
  have hConstantDifferentiable : DifferentiableOn ℝ (fun _ : ℝ => f 0) interval := by
    intro t _
    exact (hasDerivWithinAt_const (x := t) (s := interval) (c := f 0)).differentiableWithinAt
  refine eq_of_derivWithin_eq hDifferentiable hConstantDifferentiable ?_ rfl
    duration ⟨hduration, le_rfl⟩
  intro t ht
  have htInterval : t ∈ interval := ⟨ht.1, le_of_lt ht.2⟩
  have h0duration : 0 < duration := lt_of_le_of_lt ht.1 ht.2
  have hUnique := (uniqueDiffOn_Icc h0duration).uniqueDiffWithinAt htInterval
  exact (hDerivativeZero t htInterval).derivWithin hUnique |>.trans
    ((hasDerivWithinAt_const (x := t) (s := interval) (c := f 0)).derivWithin hUnique).symm

theorem preservedByDerivative_le : PreservedByDerivative (· ≤ ·) := by
  intro duration hduration f f' hDerivative hNonpositive
  let interval := Set.Icc (0 : ℝ) duration
  have hDifferentiable : DifferentiableOn ℝ f interval := by
    intro t ht
    exact (hDerivative t ht).differentiableWithinAt
  have hAntitone : AntitoneOn f interval := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 duration)
    · exact hDifferentiable.continuousOn
    · intro t ht
      exact (hDerivative t (interior_subset ht)).mono interior_subset
    · intro t ht
      exact hNonpositive t (interior_subset ht)
  exact hAntitone ⟨le_rfl, hduration⟩ ⟨hduration, le_rfl⟩ hduration

theorem preservedByDerivative_ge : PreservedByDerivative (· ≥ ·) := by
  intro duration hduration f f' hDerivative hNonnegative
  let interval := Set.Icc (0 : ℝ) duration
  have hDifferentiable : DifferentiableOn ℝ f interval := by
    intro t ht
    exact (hDerivative t ht).differentiableWithinAt
  have hMonotone : MonotoneOn f interval := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 duration)
    · exact hDifferentiable.continuousOn
    · intro t ht
      exact (hDerivative t (interior_subset ht)).mono interior_subset
    · intro t ht
      exact hNonnegative t (interior_subset ht)
  exact hMonotone ⟨le_rfl, hduration⟩ ⟨hduration, le_rfl⟩ hduration

/--
An invariant relation is preserved when derivative evolution composes with the
initial invariant relation.
-/
theorem dInvariant
    (changeRel invariantRel : ℝ → ℝ → Prop)
    (hCompose : ∀ a b c, changeRel a b → invariantRel b c → invariantRel a c)
    (hPreserved : PreservedByDerivative changeRel)
    (ode : SemanticODE σ)
    (domain pre : σ → Prop)
    (f f' : σ → ℝ)
    (hLieDerivative : HasPrime ode f f')
    (hInitial : ∀ st, pre st → invariantRel (f st) 0)
    (hDerivative : ∀ st, domain st → changeRel (f' st) 0) :
    Ensures (evolveSemantic ode domain) pre (fun st => invariantRel (f st) 0) := by
  intro initial hPre
  refine Triple.iff.mp (evolveSemantic_spec
    (Q := PostCond.noThrow fun final => ⌜invariantRel (f final) 0⌝)
      ode domain initial) ?_
  intro duration hDuration trajectory hEvolution
  have hAnalytic :
      ∀ t ∈ Set.Icc (0 : ℝ) duration,
        HasDerivWithinAt
          (fun τ => f (trajectory τ))
          (f' (trajectory t))
          (Set.Icc 0 duration) t := by
    intro t ht
    exact hLieDerivative trajectory (Set.Icc 0 duration) hEvolution.2.2 t ht
  have hDerivativeRelation :
      ∀ t ∈ Set.Icc (0 : ℝ) duration, changeRel (f' (trajectory t)) 0 := by
    intro t ht
    exact hDerivative (trajectory t) (hEvolution.2.1 t ht)
  have hEndpointRelation :=
    hPreserved duration hDuration
      (fun t => f (trajectory t))
      (fun t => f' (trajectory t))
      hAnalytic hDerivativeRelation
  have hInitialRelation : invariantRel (f (trajectory 0)) 0 := by
    simpa [hEvolution.1] using hInitial initial hPre
  exact hCompose _ _ _ hEndpointRelation hInitialRelation

end SemanticODE

open SemanticODE

/-- A relation on observables together with the derivative relation that preserves it. -/
class DInvariantRelation
    (invariantRel : ℝ → ℝ → Prop)
    (changeRel : outParam (ℝ → ℝ → Prop)) : Prop where
  compose : ∀ a b c, changeRel a b → invariantRel b c → invariantRel a c
  preserved : PreservedByDerivative changeRel

instance : DInvariantRelation Eq Eq where
  compose _ _ _ := Eq.trans
  preserved := preservedByDerivative_eq

instance : DInvariantRelation (· ≤ ·) (· ≤ ·) where
  compose _ _ _ := le_trans
  preserved := preservedByDerivative_le

instance : DInvariantRelation (· < ·) (· ≤ ·) where
  compose _ _ _ := lt_of_le_of_lt
  preserved := preservedByDerivative_le

instance : DInvariantRelation (· ≥ ·) (· ≥ ·) where
  compose _ _ _ hge₁ hge₂ := hge₂.trans hge₁
  preserved := preservedByDerivative_ge

instance : DInvariantRelation (· > ·) (· ≥ ·) where
  compose _ _ _ hge hgt := hgt.trans_le hge
  preserved := preservedByDerivative_ge

/-- Semantic differential invariant rule with relations selected by typeclass inference. -/
theorem semanticDI
    (invariantRel : ℝ → ℝ → Prop)
    {changeRel : ℝ → ℝ → Prop}
    [rule : DInvariantRelation invariantRel changeRel]
    (ode : SemanticODE σ) (domain pre : σ → Prop)
    (f f' : σ → ℝ)
    (hprime : HasPrime ode f f')
    (hinit : ∀ st, pre st → invariantRel (f st) 0)
    (hchange : ∀ st, domain st → changeRel (f' st) 0) :
    Ensures (evolveSemantic ode domain) pre (fun st => invariantRel (f st) 0) :=
  dInvariant changeRel invariantRel rule.compose rule.preserved
    ode domain pre f f' hprime hinit hchange
