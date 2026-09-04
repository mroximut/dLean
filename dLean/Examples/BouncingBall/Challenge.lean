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

theorem aerodynamic_quantum_safe :
    ∀ g H c r x v, (x ≤ H ∧ v = 0 ∧ 0 ≤ x) ∧ (0 < g ∧ c ≤ 1 ∧ 0 ≤ c ∧ 0 ≤ r) →
        ∀ x_res ∈ SetM.run (prog g c r x v), 0 ≤ x_res ∧ x_res ≤ H := sorry
