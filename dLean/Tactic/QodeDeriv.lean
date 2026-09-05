import dLean.Core.QODE
import dLean.Tactic.OdeDeriv

/-!
# QODE Derivative Tactic

This module provides `qode_deriv`, the quantified-ODE counterpart of
`ode_deriv`. It extracts derivatives of active coordinates, projects them
through product states, and applies the scalar differentiation rules.
-/

namespace dLean
open Lean Meta Elab Tactic
namespace Derivable

theorem deriv_fst
    {E₁ E₂ : Type} [Derivable I E₁] [Derivable I E₂]
    {active : Set I} {trajectory : ℝ → E₁ × E₂} {rhs : E₁ × E₂}
    {interval : Set ℝ} {t : ℝ}
    (h : has_deriv active trajectory rhs interval t) :
    has_deriv active (fun τ => (trajectory τ).1) rhs.1 interval t :=
  h.1

theorem deriv_snd
    {E₁ E₂ : Type} [Derivable I E₁] [Derivable I E₂]
    {active : Set I} {trajectory : ℝ → E₁ × E₂} {rhs : E₁ × E₂}
    {interval : Set ℝ} {t : ℝ}
    (h : has_deriv active trajectory rhs interval t) :
    has_deriv active (fun τ => (trajectory τ).2) rhs.2 interval t :=
  h.2

theorem hasDerivWithinAt_apply
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {active : Set I} {trajectory : ℝ → I → F} {rhs : I → F}
    {interval : Set ℝ} {t : ℝ}
    (h : has_deriv active trajectory rhs interval t)
    (i : I) (hi : i ∈ active) :
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

/--
`qode_deriv` proves a scalar `HasPrime` goal for a quantified ODE. It automatically
unfolds the observable, proposed derivative, evolution domain, and QODE right-hand
side. Use `qode_deriv [definitions]` to provide additional definitions or
simplification lemmas when necessary.
-/
syntax "qode_deriv" : tactic
syntax "qode_deriv" " [" term,* "]" : tactic

private def lastArg (args : Array Expr) (offset : Nat) : MetaM Expr :=
  if offset < args.size then
    pure args[args.size - 1 - offset]!
  else
    throwError "qode_deriv: malformed HasPrime goal"

private def addHeadDefinition (definitions : Array Name) (e : Expr) : Array Name :=
  match e.getAppFn.constName? with
  | some name => if definitions.contains name then definitions else definitions.push name
  | none => definitions

private def inferredDefinitions : TacticM (Array Name) := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  unless target.getAppFn.constName? == some ``HasPrime do
    throwError "qode_deriv: expected a HasPrime goal, got{indentExpr target}"
  let args := target.getAppArgs
  let semanticOde ← lastArg args 3
  let domain ← lastArg args 2
  let f ← lastArg args 1
  let fPrime ← lastArg args 0
  let qode ←
    if semanticOde.getAppFn.constName? == some ``Denotable.denotation then
      lastArg semanticOde.getAppArgs 0
    else
      pure semanticOde
  let definitions := addHeadDefinition #[] qode
  let definitions := addHeadDefinition definitions domain
  let definitions := addHeadDefinition definitions f
  return addHeadDefinition definitions fPrime

private def runQodeDeriv (definitions : Array (TSyntax `term)) : TacticM Unit := do
  let inferred ← inferredDefinitions
  let inferredSimpDefinitions ← inferred.mapM fun definition =>
    `(Lean.Parser.Tactic.simpLemma| $(mkIdent definition):term)
  let suppliedSimpDefinitions ← definitions.mapM fun definition =>
    `(Lean.Parser.Tactic.simpLemma| $(definition):term)
  let simpDefinitions := inferredSimpDefinitions ++ suppliedSimpDefinitions
  evalTactic (← `(tactic|
    (intro trajectory interval hODE hDomain t ht
     have hSt := hODE t ht
     have hDom := hDomain t ht
     simp -failIfUnchanged
       [Function.comp_apply, inner_smul_right, inner_zero_left, $simpDefinitions,*]
       at hSt hDom ⊢
     apply HasDerivWithinAt.congr_deriv <;>
       first
       | qode_deriv_step
       | (simp -failIfUnchanged
            [Pi.zero_apply, Function.comp_apply, inner_smul_right, inner_zero_left,
              $simpDefinitions,*] <;>
          ring_nf))))

elab_rules : tactic
  | `(tactic| qode_deriv) => runQodeDeriv #[]
  | `(tactic| qode_deriv [$definitions,*]) => runQodeDeriv definitions

end dLean
