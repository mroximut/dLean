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

@[simp] def invariant (created : Finset Car)
    (x v a : Car → ℝ) : Prop :=
  ∀ i ∈ created, ∀ j ∈ created,
    i ≠ j → Ordered x v a i j ∨ Ordered x v a j i

@[simp] def aGap (i j : Car) : CR3 → ℝ
  | (_, _, a) => a i - a j

@[simp] def vGap (i j : Car) : CR3 → ℝ
  | (_, v, _) => v i - v j

@[simp] def xGap (i j : Car) : CR3 → ℝ
  | (x, _, _) => x i - x j

@[simp] def vGap' (i j : Car) : CR3 → ℝ
  | (_, _, a) => a i - a j

@[simp] def xGap' (i j : Car) : CR3 → ℝ
  | (_, v, _) => v i - v j

theorem ordered_preserved (created : Finset Car) (i j : Car)
    (hi : i ∈ created) (hj : j ∈ created) :
    (fun (x, v, a) => Ordered x v a i j)
    [[evolve (motion created) dom]]
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

theorem motion_preserves_invariant (created : Finset Car) :
    (fun (x, v, a) => invariant created x v a)
    [[evolve (motion created) dom]]
    (fun (x, v, a) => invariant created x v a) := by
  apply (Ensures.iff_run _ _ _).mpr
  intro (x, v, a) hinv (x', v', a') hevo i hi j hj hij
  rcases hinv i hi j hj hij with hforw | hback
  · exact Or.inl (ordered_preserved created i j hi hj
      (x, v, a) hforw (x', v', a') hevo)
  · exact Or.inr (ordered_preserved created j i hj hi
      (x, v, a) hback (x', v', a') hevo)

theorem dccs_collision_free :
    ∀ created x v a,
      (∀ i ∈ created, ∀ j ∈ created,
        i ≠ j → Ordered x v a i j ∨ Ordered x v a j i) →
          ∀ res ∈ SetM.run (prog created x v a),
          let (created', x_res) := res
          ∀ i ∈ created', ∀ j ∈ created', i ≠ j → x_res i ≠ x_res j := by
  intro created x v a hinv res hrun
  apply SetM.of_wp_run_mem hrun
  unfold prog
  mvcgen
  intros
  mvcgen invariants
  | inv1 => ⇓⟨xs, (created, x, v, a)⟩ => ⌜invariant created x v a⌝
  case vc1.step =>
    intro _ _
    mvcgen
    simp only [WP.pure]
    apply motion_preserves_invariant
    grind [invariant]
  case vc3.vc1.post.success =>
    grind only [invariant]
