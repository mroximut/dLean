import dLean.Core.ODE
import dLean.Tactic.AutoDiff
open dLean
open Std.Do
set_option mvcgen.warning false

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
open scoped RealInnerProductSpace

@[simp] def brake (d : V) (B : ℝ) : V × ℝ → V × ℝ
  | (_x, v) => (v • d, -B)

@[simp] def dom : V × ℝ → Prop
  | (_x, v) => 0 ≤ v

def prog (B v : ℝ) (x : V) := do
  let mut (x, v) := (x, v)
  let n ← choose ℕ
  for _ in [:n] do
    let d ← choose {d : V // ‖d‖ = 1}
    (x, v) ← evolve (brake (d : V) B) dom (x, v)
  return x

@[simp] def margin (u : V) (eps B : ℝ) : V × ℝ → ℝ
  | (x, v) => v ^ 2 - 2 * B * ⟪u, x⟫ + eps

@[simp] def invariant (B : ℝ) : V × ℝ → Prop
  | (x, v) => (0 < B ∧ 0 ≤ v) ∧
    ∃ u : V, ‖u‖ = 1 ∧
      ∃ eps : ℝ, 0 < eps ∧ margin u eps B (x, v) ≤ 0

-- @[simp] def margin' (u d : V) (B : ℝ) : V × ℝ → ℝ
--   | (_x, v) => -2 * B * v * (1 + ⟪u, d⟫)

theorem margin_preserved
    (u d : V) (eps B : ℝ) (hB : 0 < B) (hu : ‖u‖ = 1) (hd : ‖d‖ = 1) :
    (fun (x, v) => margin u eps B (x, v) ≤ 0)
    [[evolve (brake d B) dom]]
    (fun (x, v) => margin u eps B (x, v) ≤ 0) := by
  apply dIle (margin u eps B)
  · autodiff
  · simp_all
  · intro (x, v) _
    have : 0 ≤ 1 + ⟪u, d⟫ := by
      linarith [neg_one_le_real_inner_of_norm_eq_one hu hd] --CS
    have : -2 * B * v ≤ 0 := by simp_all
    simp
    nlinarith

theorem evolution_preserves
    (d : V) (B : ℝ) (hB : 0 < B) (hd : ‖d‖ = 1) :
    invariant B [[evolve (brake d B) dom]] invariant B := by
  intro _ hinv
  rcases hinv with ⟨⟨_, _⟩, n, _, eps, _, _⟩
  apply dC (cut := fun st => margin n eps B st ≤ 0)
  · solve_by_elim
  · apply dW
    grind [= margin, = dom, = invariant]
  · grind [margin_preserved]

theorem initial_invariant
    (B v : ℝ) (x : V) (hpre : 0 < B ∧ 0 < v ∧ v ^ 2 / (2 * B) < ‖x‖) :
    invariant B (x, v) := by
  simp_all
  rcases hpre with ⟨hB, hv, hstop⟩
  ring_nf
  simp only [le_of_lt, hv]
  have hxnorm : 0 < ‖x‖ := by
    apply lt_trans _ hstop
    exact div_pos (pow_pos hv 2) (mul_pos (by norm_num) hB)
  have hmargin : 0 < B * ‖x‖ * 2 - v ^ 2 := by
    have h := (div_lt_iff₀ (mul_pos (by norm_num) hB)).mp hstop
    nlinarith
  let u : V := ‖x‖⁻¹ • x
  have hn_norm : ‖u‖ = 1 := by
    simp [u, norm_smul, hxnorm.ne']
  have hn_inner : ⟪u, x⟫ = ‖x‖ := by
    simp only [u, real_inner_smul_left]
    rw [real_inner_self_eq_norm_sq]
    field_simp [hxnorm.ne']
  simp_all only [norm_pos_iff, ne_eq, sub_pos, true_and]
  refine ⟨u, hn_norm, ?_⟩
  refine ⟨B * ‖x‖ * 2 - v ^ 2, sub_pos.mpr hmargin, ?_⟩
  rw [hn_inner]
  linarith

theorem vector_braking_safe :
    ∀ B v (x : V),
      0 < B ∧ 0 < v ∧ v ^ 2 / (2 * B) < ‖x‖ →
        ∀ x_res ∈ SetM.run (prog B v x), x_res ≠ 0 := by
  intro B v x hpre x' hrun
  apply SetM.of_wp_run_mem hrun
  unfold prog
  mvcgen
  intros
  mvcgen invariants
  | inv1 => ⇓⟨xs, (x, v)⟩ => ⌜invariant B (x, v)⌝
  case vc1.step =>
    intros
    mvcgen
    simp only [WP.pure]
    apply evolution_preserves
    all_goals grind [invariant]
  case vc2.vc1.pre =>
    apply initial_invariant
    assumption
  case vc3.vc1.post =>
    rename V × ℝ => st
    rename invariant B _ => hinv
    rcases hinv with ⟨_, _, _, _, _⟩
    intro _
    simp_all [margin]
    nlinarith [sq_nonneg st.2]
