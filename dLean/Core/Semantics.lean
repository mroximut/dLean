import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import dLean.Core.SetMwp
open Std.Do

abbrev HP (σ α : Type u) := σ → SetM α

instance : Union (HP σ α) where
  union p q st := p st <|> q st

def abort : SetM α := fun _ => False

def choose (α : Type u) : SetM α := Set.univ

def chooseS (S : SetM α) : SetM α := S

def test (P : Prop) : SetM Unit :=
  fun _ => P

abbrev Box (p : HP σ α) (post : α → Prop) : σ → Prop :=
  fun st => (wp⟦p st⟧ (⇓ st' => ⌜post st'⌝)).down

notation:25 "[["p"]] " post => Box p post

abbrev Ensures
    (p : HP σ α) (pre : σ → Prop) (post : α → Prop) : Prop :=
  ∀ st, pre st → (Box p post) st

notation:25 pre " [["p"]] " post => Ensures p pre post

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
  intro _ result hresult
  exact False.elim hresult

@[spec]
theorem test_spec {condition : Prop} {Q : PostCond Unit .pure} :
    ⦃⌜condition → (Q.1 ()).down⌝⦄ test condition ⦃Q⦄ := by
  apply Triple.iff.mpr
  intro h result hResult
  rcases result with ⟨⟩
  exact h hResult

theorem hp_triple_iff_safe
    (prog : HP σ α) (P : σ → Prop) (Q : α → Prop) :
    (∀ st, ⦃⌜P st⌝⦄ prog st ⦃⇓ st' => ⌜Q st'⌝⦄) ↔
      ∀ st, P st → ∀ st' ∈ SetM.run (prog st), Q st' := by
  constructor
  · intro h st
    exact (SetM.triple_iff_run (prog st) (P st) Q).mp (h st)
  · intro h st
    exact (SetM.triple_iff_run (prog st) (P st) Q).mpr (h st)

def loop (p : HP σ σ) : HP σ σ := fun st => do
  let n ← choose ℕ
  let mut st := st
  for _ in [:n] do
    st ← p st
  return st

namespace Ensures

theorem iff_run (p : HP σ α) (pre : σ → Prop) (post : α → Prop) :
    Ensures p pre post ↔
      ∀ st, pre st → ∀ st', st' ∈ SetM.run (p st) → post st' := by
  constructor
  · intro h st hPre st' hResult
    exact h st hPre st' hResult
  · intro h st hPre st' hResult
    exact h st hPre st' hResult

theorem iff_triple (p : HP σ α) (pre : σ → Prop) (post : α → Prop) :
    Ensures p pre post ↔
      ∀ st, ⦃⌜pre st⌝⦄ p st ⦃⇓ st' => ⌜post st'⌝⦄ :=
  (iff_run p pre post).trans (hp_triple_iff_safe p pre post).symm

theorem and
    {p : HP σ α} {pre : σ → Prop} {left right : α → Prop}
    (hLeft : Ensures p pre left)
    (hRight : Ensures p pre right) :
    Ensures p pre (fun st => left st ∧ right st) := by
  intro st hPre
  exact SetM.wp_and _ (hLeft st hPre) (hRight st hPre)

theorem consequence
    {p : HP σ α} {pre : σ → Prop} {post result : α → Prop}
    (hRule : Ensures p pre post)
    (hPost : ∀ st, post st → result st) :
    Ensures p pre result := by
  intro st hPre st' hResult
  exact hPost st' (hRule st hPre st' hResult)

theorem nondet_choice
    {p q : HP σ α} {pre : σ → Prop} {post : α → Prop}
    (hLeft : Ensures p pre post)
    (hRight : Ensures q pre post) :
    Ensures (p ∪ q) pre post := by
  intro st hPre
  exact SetM.wp_orElse _ _ (hLeft st hPre) (hRight st hPre)

end Ensures

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
  (∀ t ∈ Set.Icc (0 : ℝ) duration, domain (trajectory t)) ∧
  ode trajectory (Set.Icc (0 : ℝ) duration)

/--
Interpret a semantic ODE as a hybrid program
-/
def evolveSemantic
    (ode : SemanticODE σ) (domain : σ → Prop) : HP σ σ := fun st => do
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

/-- An ODE semantics is closed under restricting its time interval. -/
def RestrictionClosed {σ : Type*} (ode : SemanticODE σ) : Prop :=
  ∀ (trajectory : ℝ → σ) {smaller larger : Set ℝ}, smaller ⊆ larger →
    ode trajectory larger → ode trajectory smaller

/-- `f'` is the derivative of `f` along every trajectory of an ODE. -/
def HasDerivative
    {σ F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ode : SemanticODE σ) (f f' : σ → F) : Prop :=
  ∀ trajectory interval, ode trajectory interval →
    ∀ t ∈ interval,
      HasDerivWithinAt
      (fun τ => f (trajectory τ)) (f' (trajectory t)) interval t

/--
An ODE preserves a state relation between the initial state and
every trajectory point.
-/
def PreservesAgreement {σ : Type*}
    (ode : SemanticODE σ) (agrees : σ → σ → Prop) : Prop :=
  ∀ trajectory interval, ode trajectory interval →
    ∀ t ∈ interval, agrees (trajectory 0) (trajectory t)

namespace SemanticODE

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

/--
An invariant relation is preserved when derivative evolution composes with the
initial invariant relation.
-/
theorem dInvariant
    (change invariant : ℝ → ℝ → Prop)
    (hCompose : ∀ a b c, change a b → invariant b c → invariant a c)
    (hPreserved : PreservedByDerivative change)
    (ode : SemanticODE σ)
    (domain pre : σ → Prop)
    (f f' : σ → ℝ)
    (hLieDerivative : HasDerivative ode f f')
    (hInitial : ∀ st, pre st → invariant (f st) 0)
    (hDerivative : ∀ st, domain st → change (f' st) 0) :
    Ensures (evolveSemantic ode domain) pre (fun st => invariant (f st) 0) := by
  intro initial hPre
  refine Triple.iff.mp (evolveSemantic_spec
    (Q := PostCond.noThrow fun final => ⌜invariant (f final) 0⌝)
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
      ∀ t ∈ Set.Icc (0 : ℝ) duration, change (f' (trajectory t)) 0 := by
    intro t ht
    exact hDerivative (trajectory t) (hEvolution.2.1 t ht)
  have hEndpointRelation :=
    hPreserved duration hDuration
      (fun t => f (trajectory t))
      (fun t => f' (trajectory t))
      hAnalytic hDerivativeRelation
  have hInitialRelation : invariant (f (trajectory 0)) 0 := by
    simpa [hEvolution.1] using hInitial initial hPre
  exact hCompose _ _ _ hEndpointRelation hInitialRelation

/-- Semantic differential invariant rule for equality observables. -/
theorem dInvariantEq
    (ode : SemanticODE σ) (domain pre : σ → Prop)
    (f f' : σ → ℝ) (hLieDerivative : HasDerivative ode f f')
    (hInitial : ∀ st, pre st → f st = 0)
    (hDerivative : ∀ st, domain st → f' st = 0) :
    Ensures (evolveSemantic ode domain) pre (fun st => f st = 0) :=
  dInvariant Eq Eq (fun _ _ _ => Eq.trans) preservedByDerivative_eq
    ode domain pre f f' hLieDerivative hInitial hDerivative

/-- Semantic differential invariant rule for nonincreasing scalar observables. -/
theorem dInvariantLe
    (ode : SemanticODE σ) (domain pre : σ → Prop)
    (f f' : σ → ℝ) (hLieDerivative : HasDerivative ode f f')
    (hInitial : ∀ st, pre st → f st ≤ 0)
    (hDerivative : ∀ st, domain st → f' st ≤ 0) :
    Ensures (evolveSemantic ode domain) pre (fun st => f st ≤ 0) :=
  dInvariant (· ≤ ·) (· ≤ ·) (fun _ _ _ => le_trans) preservedByDerivative_le
    ode domain pre f f' hLieDerivative hInitial hDerivative

/-- Semantic differential invariant rule for strict sublevel observables. -/
theorem dInvariantLt
    (ode : SemanticODE σ) (domain pre : σ → Prop)
    (f f' : σ → ℝ) (hLieDerivative : HasDerivative ode f f')
    (hInitial : ∀ st, pre st → f st < 0)
    (hDerivative : ∀ st, domain st → f' st ≤ 0) :
    Ensures (evolveSemantic ode domain) pre (fun st => f st < 0) :=
  dInvariant (· ≤ ·) (· < ·) (fun _ _ _ => lt_of_le_of_lt) preservedByDerivative_le
    ode domain pre f f' hLieDerivative hInitial hDerivative

end SemanticODE
