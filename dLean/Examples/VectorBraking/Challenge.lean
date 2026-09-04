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

theorem vector_braking_safe :
    ∀ B v (x : V),
      0 < B ∧ 0 < v ∧ v ^ 2 / (2 * B) < ‖x‖ →
        ∀ x_res ∈ SetM.run (prog B v x), x_res ≠ 0 := sorry
