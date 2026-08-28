import Mathlib.Data.Set.Functor
import Std.Tactic.Do

/-!
A universal weakest-precondition interpretation for mathlib's powerset monad `SetM`.
This is the demonic interpretation of nondeterminism: every possible result must
satisfy the postcondition.
-/

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

theorem SetM.triple_iff_run
    (p : SetM α) (P : Prop) (Q : α → Prop) :
    (⦃⌜P⌝⦄ p ⦃⇓ x => ⌜Q x⌝⦄) ↔ (P → ∀ x ∈ SetM.run p, Q x) := by
  constructor
  · intro h hP x hx
    exact Triple.iff.mp h hP x hx
  · intro h
    apply Triple.iff.mpr
    intro hP x hx
    exact h hP x hx

theorem SetM.of_wp_run_mem
    {p : SetM α} {result : α} (hResult : result ∈ SetM.run p) (post : α → Prop)
    (hWP : (wp⟦p⟧ (⇓result => ⌜post result⌝)).down) : post result := by
  exact hWP result hResult

theorem SetM.wp_orElse (xs ys : SetM α) {Q : PostCond α .pure}
    (hxs : (wp⟦xs⟧ Q).down) (hys : (wp⟦ys⟧ Q).down) :
    (wp⟦xs <|> ys⟧ Q).down := by
  intro result hresult
  change result ∈ SetM.run xs ∪ SetM.run ys at hresult
  rcases hresult with hresult | hresult
  · exact hxs result hresult
  · exact hys result hresult

theorem SetM.wp_and (xs : SetM α) {P Q : PostCond α .pure}
    (hP : (wp⟦xs⟧ P).down) (hQ : (wp⟦xs⟧ Q).down) :
    (wp⟦xs⟧ (P ∧ₚ Q)).down := by
  intro result hresult
  exact ⟨hP result hresult, hQ result hresult⟩
