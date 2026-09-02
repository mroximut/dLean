import dLean.Core.QODE
import dLean.Tactic.QodeDeriv
open Std.Do
set_option mvcgen.warning false

abbrev Car := Nat
abbrev CR3 := (Car → ℝ) × (Car → ℝ) × (Car → ℝ)

@[simp] def motion (created : Finset Car) : Set Car × (CR3 → CR3) :=
  (created, fun (_x, v, a) => (v, a, 0))

@[simp] def dom (_ : CR3) : Prop := True

@[reducible] def Ordered (x v a : Car → ℝ) (i j : Car) : Prop :=
  x i < x j ∧ v i ≤ v j ∧ a i ≤ a j

def prog (created : Finset Car) (x v a : Car → ℝ) := do
  let mut created := created
  let mut (x, v, a) := (x, v, a)
  let n ← choose ℕ
  for _ in [:n] do
    let i ← chooseS {i | i ∉ created}
    created := insert i created
    unless (∀ j ∈ created, i ≠ j →
            Ordered x v a i j ∨ Ordered x v a j i) do abort
    (x, v, a) ← evolve (motion created) dom (x, v, a)
  return (created, x)

theorem dccs_collision_free :
    ∀ created x v a,
      (∀ i ∈ created, ∀ j ∈ created,
        i ≠ j → Ordered x v a i j ∨ Ordered x v a j i) →
          ∀ res ∈ SetM.run (prog created x v a),
          let (created', x_res) := res
          ∀ i ∈ created', ∀ j ∈ created', i ≠ j → x_res i ≠ x_res j := sorry
