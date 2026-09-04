import dLean.Core.QODE
import dLean.Tactic.QodeDeriv
open dLean
open Std.Do
set_option mvcgen.warning false

abbrev Car := Nat
abbrev CarState := ℝ × ℝ × ℝ

@[simp] def x (f : Car → CarState) (car : Car) : ℝ := (f car).1
@[simp] def v (f : Car → CarState) (car : Car) : ℝ := (f car).2.1
@[simp] def a (f : Car → CarState) (car : Car) : ℝ := (f car).2.2

@[simp] def motion (created : Finset Car) :
    Set Car × ((Car → CarState) → (Car → CarState)) :=
  (created, fun f => fun car =>
              (v f car, a f car, 0))

@[simp] def dom (_ : Car → CarState) : Prop := True

@[reducible] def Ordered (f : Car → CarState) (i j : Car) : Prop :=
  x f i < x f j ∧ v f i ≤ v f j ∧ a f i ≤ a f j

def prog (created : Finset Car) (f : Car → CarState) := do
  let mut created := created
  let mut f := f
  let n ← choose ℕ
  for _ in [:n] do
    let i ← chooseS {i | i ∉ created}
    created := insert i created
    unless (∀ j ∈ created, i ≠ j →
        Ordered f i j ∨ Ordered f j i) do abort
    f ← evolve (motion created) dom f
  return (created, fun car => x f car)

@[simp] def invariant (created : Finset Car) (f : Car → CarState) : Prop :=
  ∀ i ∈ created, ∀ j ∈ created,
    i ≠ j → Ordered f i j ∨ Ordered f j i

@[simp] def aGap (i j : Car) (f : Car → CarState) : ℝ :=
  a f i - a f j

@[simp] def vGap (i j : Car) (f : Car → CarState) : ℝ :=
  v f i - v f j

@[simp] def xGap (i j : Car) (f : Car → CarState) : ℝ :=
  x f i - x f j

@[simp] def vGap' (i j : Car) (f : Car → CarState) : ℝ :=
  a f i - a f j

@[simp] def xGap' (i j : Car) (f : Car → CarState) : ℝ :=
  v f i - v f j

theorem ordered_preserved (created : Finset Car) (i j : Car)
    (hi : i ∈ created) (hj : j ∈ created) :
    (fun f => Ordered f i j)
    [[evolve (motion created) dom]]
    (fun f => Ordered f i j) := by
  apply dC (cut := fun f => aGap i j f ≤ 0)
  · apply dIle (aGap i j) (fun _ => 0)
    · qode_deriv [aGap, a, motion]
    · grind only [aGap]
    · simp
  · apply dC (cut := fun f => vGap i j f ≤ 0)
    · apply dIle (vGap i j) (vGap' i j)
      · qode_deriv [vGap, vGap', v, a, motion]
      · grind only [vGap]
      · grind only [aGap, vGap']
    · apply dC (cut := fun f => xGap i j f < 0)
      · apply dIlt (xGap i j) (xGap' i j)
        · qode_deriv [xGap, xGap', x, v, a, motion]
        · grind only [xGap]
        · grind only [vGap, xGap']
      · apply dW
        grind only [aGap, xGap, vGap]

theorem motion_preserves_invariant (created : Finset Car) :
    invariant created
    [[evolve (motion created) dom]]
    invariant created := by
  apply (Ensures.iff_run _ _ _).mpr
  intro f hInvariant f' hEvolution i hi j hj hij
  rcases hInvariant i hi j hj hij with hForward | hBackward
  · exact Or.inl (ordered_preserved created i j hi hj
      f hForward f' hEvolution)
  · exact Or.inr (ordered_preserved created j i hj hi
      f hBackward f' hEvolution)

theorem dccs_collision_free :
    ∀ created f, invariant created f →
      ∀ res ∈ SetM.run (prog created f),
        let (created', x_res) := res
        ∀ i ∈ created', ∀ j ∈ created', i ≠ j → x_res i ≠ x_res j := by
  intro created f hinv res hrun
  apply SetM.of_wp_run_mem hrun
  unfold prog
  mvcgen
  intros
  mvcgen invariants
  | inv1 => ⇓⟨xs, (created, f)⟩ => ⌜invariant created f⌝
  case vc1.step =>
    intro _ _
    mvcgen
    simp only [WP.pure]
    apply motion_preserves_invariant
    grind [invariant]
  case vc3.vc1.post.success =>
    grind only [invariant, x]
