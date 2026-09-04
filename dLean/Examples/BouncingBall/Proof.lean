import dLean.Core.ODE
import dLean.Tactic.AutoDiff
open dLean
open Std.Do
set_option mvcgen.warning false

@[simp] def up (g r : ℝ) : ℝ × ℝ → ℝ × ℝ
  | (_x, v) => (v, -g - r * v ^ 2)

@[simp] def updom : ℝ × ℝ → Prop
  | (x, v) => 0 ≤ x ∧ 0 ≤ v

@[simp] def down (g r : ℝ) : ℝ × ℝ → ℝ × ℝ
  | (_x, v) => (v, -g + r * v ^ 2)

@[simp] def downdom : ℝ × ℝ → Prop
  | (x, v) => 0 ≤ x ∧ v ≤ 0

def prog (g c r x v : ℝ) := do
  let mut (x, v) := (x, v)
  let n ← choose ℕ
  for _ in [:n] do
    if x = 0 then
      v := -c * v
    (x, v) ← (evolve (up g r) updom ∪ evolve (down g r) downdom) (x, v)
  return x

@[simp] def energyGap (g H : ℝ) : ℝ × ℝ → ℝ
  | (x, v) => v ^ 2 + 2 * g * x - 2 * g * H

-- @[simp] def upEnergyGap' (g r : ℝ) : ℝ × ℝ → ℝ
--   | (_x, v) => 2 * v * (-g - r * v ^ 2) + 2 * g * v

-- @[simp] def downEnergyGap' (g r : ℝ) : ℝ × ℝ → ℝ
--   | (_x, v) => 2 * v * (-g + r * v ^ 2) + 2 * g * v

@[simp] def invariant (g H : ℝ) : ℝ × ℝ → Prop
  | (x, v) => energyGap g H (x, v) ≤ 0 ∧ 0 ≤ x

theorem upward_preserves (g H r : ℝ) (hr : 0 ≤ r) :
    invariant g H [[evolve (up g r) updom]] invariant g H := by
  apply dC (cut := fun (x, v) => energyGap g H (x, v) ≤ 0)
  · apply dIle (energyGap g H)
    · autodiff
    · simp_all
    · intro (x, v) _
      simp
      ring_nf
      have : 0 ≤ v ^ 3 := by simp_all
      nlinarith
  · apply dW
    simp_all

theorem downward_preserves (g H r : ℝ) (hr : 0 ≤ r) :
    invariant g H [[evolve (down g r) downdom]] invariant g H := by
  apply dC (cut := fun (x, v) => energyGap g H (x, v) ≤ 0)
  · apply dIle (energyGap g H)
    · autodiff
    · simp_all
    · intro (x, v) _
      simp
      ring_nf
      have : v ^ 3 ≤ 0 := by
        simp_all [Odd.pow_nonpos (n := 3) (by decide)]
      nlinarith
  · apply dW
    simp_all

theorem continuous_preserves (hr : 0 ≤ r) :
    invariant g H
    [[evolve (up g r) updom ∪ evolve (down g r) downdom]]
    invariant g H := by
  apply Ensures.nondet_choice
  · apply upward_preserves
    simp_all
  · apply downward_preserves
    simp_all

theorem aerodynamic_quantum_safe :
    ∀ g H c r x v, (x ≤ H ∧ v = 0 ∧ 0 ≤ x) ∧ (0 < g ∧ c ≤ 1 ∧ 0 ≤ c ∧ 0 ≤ r) →
      ∀ x_res ∈ SetM.run (prog g c r x v), 0 ≤ x_res ∧ x_res ≤ H := by
  intro g H c r x v hpre res hrun
  apply SetM.of_wp_run_mem hrun
  unfold prog
  mvcgen
  intros
  mvcgen invariants
  | inv1 => ⇓⟨xs, (x, v)⟩ => ⌜invariant g H (x, v)⌝
  case vc1.step.isTrue =>
    simp only [WP.pure]
    apply continuous_preserves (by simp_all)
    simp_all
    have : c ^ 2 ≤ 1 := by simp_all [pow_le_one₀]
    nlinarith
  case vc2.step.isFalse =>
    simp only [WP.pure]
    apply continuous_preserves (by simp_all)
    simp_all
  case vc3.vc1.pre =>
    simp_all
  case vc4.vc1.post.success =>
    simp_all
    nlinarith
