import dLean.Core.QODE
import dLean.Tactic.QodeDeriv

/-!
# Collision freedom for a growing collection of cars

Example from https://symbolaris.com/pub/QdL.pdf

Consider cars moving along a line, with natural numbers as identifiers. The
finite set `active` records which cars are present, and `x i`, `v i`,
and `a i` give the position, velocity, and acceleration of car `i`. Each
loop iteration creates a new car whose position, velocity, and
acceleration satisfies some consition w.r.t. every existing car.

This module proves `collision_freedom`: if the initial cars satisfy the
pairwise ordering condition, then distinct active cars have distinct positions
after any finite number of loop iterations. The ordering condition requires
that, for each pair, the car with the smaller position also has no greater
velocity or acceleration.

The loop invariant maintains this ordering for every distinct pair of active
cars. Ordered accelerations preserve the velocity ordering, which in turn
preserves the strict position ordering. The insertion check establishes the
condition for each new pair, and strict position ordering excludes collisions.
-/

open dLean
open Std.Do
set_option mvcgen.warning false

abbrev Car := Nat
abbrev State := (Car → ℝ) × (Car → ℝ) × (Car → ℝ)

@[simp] def motion (active : Finset Car) : Set Car × (State → State) :=
  (active, fun (_x, v, a) => (v, a, 0))

@[simp] def domain (_ : State) : Prop := True

@[reducible] def Ordered (x v a : Car → ℝ) (i j : Car) : Prop :=
  x i < x j ∧ v i ≤ v j ∧ a i ≤ a j

def prog (active : Finset Car) (x v a : Car → ℝ) := do
  let mut active := active
  let mut (x, v, a) := (x, v, a)
  let n ← choose ℕ
  for _ in [:n] do
    let i ← chooseS {i | i ∉ active}
    active := insert i active
    unless (∀ j ∈ active, i ≠ j →
        Ordered x v a i j ∨ Ordered x v a j i) do abort
    (x, v, a) ← evolve (motion active) domain (x, v, a)
  return (active, x)

@[simp] def invariant (active : Finset Car)
    (x v a : Car → ℝ) : Prop :=
  ∀ i ∈ active, ∀ j ∈ active,
    i ≠ j → Ordered x v a i j ∨ Ordered x v a j i

@[simp] def aGap (i j : Car) : State → ℝ
  | (_, _, a) => a i - a j

@[simp] def vGap (i j : Car) : State → ℝ
  | (_, v, _) => v i - v j

@[simp] def xGap (i j : Car) : State → ℝ
  | (x, _, _) => x i - x j

@[simp] def vGap' (i j : Car) : State → ℝ
  | (_, _, a) => a i - a j

@[simp] def xGap' (i j : Car) : State → ℝ
  | (_, v, _) => v i - v j

theorem ordered_preserved (active : Finset Car) (i j : Car)
    (hi : i ∈ active) (hj : j ∈ active) :
    (fun (x, v, a) => Ordered x v a i j)
    [[evolve (motion active) domain]]
    (fun (x, v, a) => Ordered x v a i j) := by
  apply dC (cut := fun st => aGap i j st ≤ 0)
  · apply dIle (aGap i j) (fun _ => 0)
    · qode_deriv [aGap, motion]
    · grind only [aGap]
    · simp
  · apply dC (cut := fun st => vGap i j st ≤ 0)
    · apply dIle (vGap i j) (vGap' i j)
      · qode_deriv [vGap', motion]
      · grind only [vGap]
      · grind only [aGap, vGap']
    · apply dC (cut := fun st => xGap i j st < 0)
      · apply dIlt (xGap i j) (xGap' i j)
        · qode_deriv [xGap', motion]
        · grind only [xGap]
        · grind only [vGap, xGap']
      · apply dW
        grind only [aGap, xGap, vGap]

theorem motion_preserves_invariant (active : Finset Car) :
    (fun (x, v, a) => invariant active x v a)
    [[evolve (motion active) domain]]
    (fun (x, v, a) => invariant active x v a) := by
  apply (Ensures.iff_run _ _ _).mpr
  intro (x, v, a) hinv (x', v', a') hevo i hi j hj hij
  rcases hinv i hi j hj hij with hforw | hback
  · exact Or.inl (ordered_preserved active i j hi hj
      (x, v, a) hforw (x', v', a') hevo)
  · exact Or.inr (ordered_preserved active j i hj hi
      (x, v, a) hback (x', v', a') hevo)

theorem collision_freedom :
    ∀ active x v a,
      (∀ i ∈ active, ∀ j ∈ active,
        i ≠ j → Ordered x v a i j ∨ Ordered x v a j i) →
          ∀ res ∈ SetM.run (prog active x v a),
          let (active', x_res) := res
          ∀ i ∈ active', ∀ j ∈ active', i ≠ j → x_res i ≠ x_res j := by
  intro active x v a hinv res hrun
  apply SetM.of_wp_run_mem hrun
  unfold prog
  mvcgen
  intros
  mvcgen invariants
  | inv1 => ⇓⟨xs, (active, x, v, a)⟩ => ⌜invariant active x v a⌝
  case vc1.step =>
    intro _ _
    mvcgen
    simp only [WP.pure]
    apply motion_preserves_invariant
    grind [invariant]
  case vc3.vc1.post.success =>
    grind only [invariant]
