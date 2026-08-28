import dLean.Core.Qode
import dLean.Tactic.OdeDeriv

namespace Coordinatewise

/-- Project a coordinatewise derivative through the first component of a product. -/
theorem deriv_fst
    {E₁ E₂ : Type} [Coordinatewise I E₁] [Coordinatewise I E₂]
    {created : Set I} {trajectory : ℝ → E₁ × E₂} {rhs : E₁ × E₂}
    {interval : Set ℝ} {t : ℝ}
    (h : deriv created trajectory rhs interval t) :
    deriv created (fun τ => (trajectory τ).1) rhs.1 interval t :=
  h.1

/-- Project a coordinatewise derivative through the second component of a product. -/
theorem deriv_snd
    {E₁ E₂ : Type} [Coordinatewise I E₁] [Coordinatewise I E₂]
    {created : Set I} {trajectory : ℝ → E₁ × E₂} {rhs : E₁ × E₂}
    {interval : Set ℝ} {t : ℝ}
    (h : deriv created trajectory rhs interval t) :
    deriv created (fun τ => (trajectory τ).2) rhs.2 interval t :=
  h.2

/-- Extract the derivative of one active coordinate from a function-valued state. -/
theorem hasDerivWithinAt_apply
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {created : Set I} {trajectory : ℝ → I → F} {rhs : I → F}
    {interval : Set ℝ} {t : ℝ}
    (h : deriv created trajectory rhs interval t)
    (i : I) (hi : i ∈ created) :
    HasDerivWithinAt (fun τ => trajectory τ i) (rhs i) interval t :=
  h i hi

end Coordinatewise

syntax "qode_deriv_step" : tactic

macro_rules
  | `(tactic| qode_deriv_step) =>
      `(tactic|
        first
        | assumption
        | (apply OdeDeriv.hasDerivWithinAt_add_apply <;> qode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_sub_apply <;> qode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_neg_apply <;> qode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_pow_apply <;> qode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_sin_apply <;> qode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_cos_apply <;> qode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_mul_apply <;> qode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_inner_apply <;> qode_deriv_step)
        | (apply Coordinatewise.hasDerivWithinAt_apply <;>
            first
            | assumption
            | solve_by_elim [Coordinatewise.deriv_fst, Coordinatewise.deriv_snd])
        | apply hasDerivWithinAt_const)

/-- Prove a scalar `HasDerivative` goal along an indexed QODE. -/
syntax "qode_deriv" " [" term,* "]" : tactic

macro_rules
  | `(tactic| qode_deriv [$definitions,*]) => do
      let simpDefinitions ← definitions.getElems.mapM fun definition =>
        `(Lean.Parser.Tactic.simpLemma| $(definition):term)
      `(tactic|
        (intro trajectory interval hODE t ht
         have hSt := hODE t ht
         simp -failIfUnchanged only [Function.comp_apply, $simpDefinitions,*] at hSt ⊢
         apply HasDerivWithinAt.congr_deriv <;>
           first
           | qode_deriv_step
           | (simp -failIfUnchanged only
                [Pi.zero_apply, Function.comp_apply, $simpDefinitions,*] <;>
              ring)))
