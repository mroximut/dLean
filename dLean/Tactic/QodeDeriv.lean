import dLean.Core.QODE
import dLean.Tactic.OdeDeriv

namespace dLean
namespace Derivable

/-- Project a coordinatewise derivative through the first component of a product. -/
theorem deriv_fst
    {E₁ E₂ : Type} [Derivable I E₁] [Derivable I E₂]
    {created : Set I} {trajectory : ℝ → E₁ × E₂} {rhs : E₁ × E₂}
    {interval : Set ℝ} {t : ℝ}
    (h : has_deriv created trajectory rhs interval t) :
    has_deriv created (fun τ => (trajectory τ).1) rhs.1 interval t :=
  h.1

/-- Project a coordinatewise derivative through the second component of a product. -/
theorem deriv_snd
    {E₁ E₂ : Type} [Derivable I E₁] [Derivable I E₂]
    {created : Set I} {trajectory : ℝ → E₁ × E₂} {rhs : E₁ × E₂}
    {interval : Set ℝ} {t : ℝ}
    (h : has_deriv created trajectory rhs interval t) :
    has_deriv created (fun τ => (trajectory τ).2) rhs.2 interval t :=
  h.2

/-- Extract the derivative of one active coordinate from a function-valued state. -/
theorem hasDerivWithinAt_apply
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {created : Set I} {trajectory : ℝ → I → F} {rhs : I → F}
    {interval : Set ℝ} {t : ℝ}
    (h : has_deriv created trajectory rhs interval t)
    (i : I) (hi : i ∈ created) :
    HasDerivWithinAt (fun τ => trajectory τ i) (rhs i) interval t :=
  h i hi

end Derivable

syntax "qode_deriv_step" : tactic

macro_rules
  | `(tactic| qode_deriv_step) =>
      `(tactic|
        first
        | assumption
        | solve_by_elim [Derivable.hasDerivWithinAt_apply,
            Derivable.deriv_fst, Derivable.deriv_snd,
            OdeDeriv.hasDerivWithinAt_fst, OdeDeriv.hasDerivWithinAt_snd]
        | (apply OdeDeriv.hasDerivWithinAt_add_apply <;> qode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_sub_apply <;> qode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_neg_apply <;> qode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_pow_apply <;> qode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_sin_apply <;> qode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_cos_apply <;> qode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_mul_apply <;> qode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_inner_apply <;> qode_deriv_step)
        | (apply Derivable.hasDerivWithinAt_apply <;>
            first
            | assumption
            | solve_by_elim [Derivable.deriv_fst, Derivable.deriv_snd])
        | apply hasDerivWithinAt_const)

/-- Prove a scalar `HasPrime` goal along an indexed QODE. -/
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
              ring_nf)))

end dLean
