import Mathlib.Data.Set.Functor
import Std.Tactic.Do

/-!
# SetMWP

A weakest-precondition interpretation for the set monad `SetM`. Monadic
`SetM` programs can be thought of as nondeterministic programs where the
output set contains the results from every possible run of the program. This
is the demonic interpretation of nondeterminism, so the weakest precondition
with respect to a given postcondition requires every possible result to
satisfy that postcondition. Implementing the typeclasses `WP` and `WPMonad`
enables the usage of `mvcgen` framework in proofs involving monadic
`SetM` programs.

As an example, `(wp⟦p⟧ (⇓res => ⌜Q res⌝)).down` for a set `p` is defined
to mean the same as `∀ x ∈ SetM.run p, Q x`. That means every element
in `p` (in other words every possible result of the nondeterministic
monadic program `p`) satisfies Q.
-/

namespace dLean
open Std.Do

instance : WP SetM .pure where
  wp xs :=
    { trans := fun Q => ⌜∀ a, a ∈ SetM.run xs → (Q.1 a).down⌝
      conjunctiveRaw := by
        intro Q₁ Q₂
        change (∀ a ∈ SetM.run xs, (Q₁.1 a).down ∧ (Q₂.1 a).down) ↔
          (∀ a ∈ SetM.run xs, (Q₁.1 a).down) ∧ ∀ a ∈ SetM.run xs, (Q₂.1 a).down
        constructor
        · intro h
          exact ⟨fun a ha => (h a ha).1, fun a ha => (h a ha).2⟩
        · rintro ⟨h₁, h₂⟩ a ha
          exact ⟨h₁ a ha, h₂ a ha⟩ }

instance : WPMonad SetM .pure where
  wp_pure a := by
    ext Q
    change (∀ x ∈ ({a} : Set _), (Q.1 x).down) ↔ (Q.1 a).down
    simp
  wp_bind xs f := by
    ext Q
    change (∀ y ∈ SetM.run (xs >>= f), (Q.1 y).down) ↔
      ∀ x ∈ SetM.run xs, ∀ y ∈ SetM.run (f x), (Q.1 y).down
    change (∀ y ∈ ⋃ x ∈ SetM.run xs, SetM.run (f x), (Q.1 y).down) ↔ _
    simp only [Set.mem_iUnion]
    constructor
    · intro h x hx y hy
      exact h y ⟨x, hx, hy⟩
    · intro h y hy
      rcases hy with ⟨x, hx, hy⟩
      exact h x hx y hy

theorem SetM.wp_iff_run
  (p : SetM α) (Q : α → Prop) :
  ((wp⟦p⟧ (⇓res => ⌜Q res⌝)).down) ↔ (∀ x ∈ SetM.run p, Q x) := by rfl

theorem SetM.of_wp_run_mem
    {p : SetM α} {res : α} (hres : res ∈ SetM.run p) (post : α → Prop)
    (hWP : (wp⟦p⟧ (⇓res => ⌜post res⌝)).down) : post res := by
  exact hWP res hres

theorem SetM.wp_orElse
    (S S' : SetM α) {Q : PostCond α .pure}
    (hxs : (wp⟦S⟧ Q).down) (hys : (wp⟦S'⟧ Q).down) :
    (wp⟦S <|> S'⟧ Q).down := by
  intro res hres
  rcases hres with hres | hres
  · exact hxs res hres
  · exact hys res hres

theorem SetM.wp_and (S : SetM α) {P Q : PostCond α .pure}
    (hP : (wp⟦S⟧ P).down) (hQ : (wp⟦S⟧ Q).down) :
    (wp⟦S⟧ (P ∧ₚ Q)).down := by
  intro res hres
  exact ⟨hP res hres, hQ res hres⟩

end dLean
