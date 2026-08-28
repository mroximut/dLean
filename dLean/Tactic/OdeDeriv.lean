import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring
import dLean.Core.Ode

open scoped RealInnerProductSpace

namespace OdeDeriv

theorem hasDerivWithinAt_fst
    {A B : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {f : ℝ → A × B} {f' : A × B} {interval : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt f f' interval t) :
    HasDerivWithinAt (fun τ => (f τ).1) f'.1 interval t := by
  simpa using h.hasFDerivWithinAt.fst.hasDerivWithinAt

theorem hasDerivWithinAt_snd
    {A B : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {f : ℝ → A × B} {f' : A × B} {interval : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt f f' interval t) :
    HasDerivWithinAt (fun τ => (f τ).2) f'.2 interval t := by
  simpa using h.hasFDerivWithinAt.snd.hasDerivWithinAt

theorem hasDerivWithinAt_apply
    {I A : Type} [Finite I] [NormedAddCommGroup A] [NormedSpace ℝ A]
    {f : ℝ → I → A} {f' : I → A} {interval : Set ℝ} {t : ℝ}
    (index : I) (h : HasDerivWithinAt f f' interval t) :
    HasDerivWithinAt (fun τ => f τ index) (f' index) interval t := by
  let _ := Fintype.ofFinite I
  have hCoordinate :=
    (ContinuousLinearMap.proj index).hasFDerivAt.comp_hasDerivWithinAt t h
  simpa [Function.comp_def] using hCoordinate

theorem hasDerivWithinAt_add_apply
    {f g : ℝ → ℝ} {f' g' : ℝ} {interval : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' interval t)
    (hg : HasDerivWithinAt g g' interval t) :
    HasDerivWithinAt (fun τ => f τ + g τ) (f' + g') interval t := by
  with_reducible_and_instances exact hf.add hg

theorem hasDerivWithinAt_sub_apply
    {f g : ℝ → ℝ} {f' g' : ℝ} {interval : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' interval t)
    (hg : HasDerivWithinAt g g' interval t) :
    HasDerivWithinAt (fun τ => f τ - g τ) (f' - g') interval t := by
  with_reducible_and_instances exact hf.sub hg

theorem hasDerivWithinAt_mul_apply
    {f g : ℝ → ℝ} {f' g' : ℝ} {interval : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' interval t)
    (hg : HasDerivWithinAt g g' interval t) :
    HasDerivWithinAt (fun τ => f τ * g τ) (f' * g t + f t * g') interval t := by
  with_reducible_and_instances exact hf.mul hg

theorem hasDerivWithinAt_inner_apply
    {G : Type} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    {f g : ℝ → G} {f' g' : G} {interval : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' interval t)
    (hg : HasDerivWithinAt g g' interval t) :
    HasDerivWithinAt (fun τ => ⟪f τ, g τ⟫) (⟪f t, g'⟫ + ⟪f', g t⟫) interval t := by
  exact hf.inner ℝ hg

theorem hasDerivWithinAt_neg_apply
    {f : ℝ → ℝ} {f' : ℝ} {interval : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' interval t) :
    HasDerivWithinAt (fun τ => -f τ) (-f') interval t := by
  with_reducible_and_instances exact hf.neg

theorem hasDerivWithinAt_pow_apply
    {f : ℝ → ℝ} {f' : ℝ} {interval : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' interval t) (n : ℕ) :
    HasDerivWithinAt (fun τ => f τ ^ n) (n * f t ^ (n - 1) * f') interval t := by
  with_reducible_and_instances exact hf.pow n

theorem hasDerivWithinAt_sin_apply
    {f : ℝ → ℝ} {f' : ℝ} {interval : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' interval t) :
    HasDerivWithinAt (fun τ => Real.sin (f τ)) (Real.cos (f t) * f') interval t := by
  with_reducible_and_instances exact hf.sin

theorem hasDerivWithinAt_cos_apply
    {f : ℝ → ℝ} {f' : ℝ} {interval : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' interval t) :
    HasDerivWithinAt (fun τ => Real.cos (f τ)) (-Real.sin (f t) * f') interval t := by
  with_reducible_and_instances exact hf.cos

end OdeDeriv

syntax "ode_deriv_step" : tactic

macro_rules
  | `(tactic| ode_deriv_step) =>
      `(tactic|
        first
        | assumption
        | (apply OdeDeriv.hasDerivWithinAt_add_apply <;> ode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_sub_apply <;> ode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_neg_apply <;> ode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_pow_apply <;> ode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_sin_apply <;> ode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_cos_apply <;> ode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_mul_apply <;> ode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_inner_apply <;> ode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_fst <;> ode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_snd <;> ode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_apply <;> ode_deriv_step)
        | apply hasDerivWithinAt_const)

/-- Prove a scalar `HasDerivative` goal along an ordinary vector-field ODE. -/
syntax "ode_deriv" " [" term,* "]" : tactic

macro_rules
  | `(tactic| ode_deriv [$definitions,*]) => do
      let simpDefinitions ← definitions.getElems.mapM fun definition =>
        `(Lean.Parser.Tactic.simpLemma| $(definition):term)
      `(tactic|
        (intro trajectory interval hODE t ht
         have hSt := hODE t ht
         simp -failIfUnchanged only [Function.comp_apply, $simpDefinitions,*] at hSt ⊢
         apply HasDerivWithinAt.congr_deriv <;>
           first
           | ode_deriv_step
           | (simp -failIfUnchanged only [Function.comp_apply, $simpDefinitions,*] <;>
              ring_nf)))
