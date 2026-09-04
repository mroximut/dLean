import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring
import dLean.Core.ODE

/-!
# ODE Derivative Tactic

This module provides `ode_deriv`, a tactic for proving scalar `HasPrime` goals
for ordinary ODEs. It derives the result from the ODE's trajectory equation
using standard differentiation rules and polynomial normalization.
-/

namespace dLean

open Lean Meta Elab Tactic
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
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f g : ℝ → G} {f' g' : G} {interval : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' interval t)
    (hg : HasDerivWithinAt g g' interval t) :
    HasDerivWithinAt (fun τ => f τ + g τ) (f' + g') interval t := by
  with_reducible_and_instances exact hf.add hg

theorem hasDerivWithinAt_sub_apply
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f g : ℝ → G} {f' g' : G} {interval : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' interval t)
    (hg : HasDerivWithinAt g g' interval t) :
    HasDerivWithinAt (fun τ => f τ - g τ) (f' - g') interval t := by
  with_reducible_and_instances exact hf.sub hg

theorem hasDerivWithinAt_smul_apply
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : ℝ → ℝ} {g : ℝ → G} {f' : ℝ} {g' : G} {interval : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' interval t)
    (hg : HasDerivWithinAt g g' interval t) :
    HasDerivWithinAt (fun τ => f τ • g τ) (f t • g' + f' • g t) interval t := by
  with_reducible_and_instances exact hf.smul hg

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
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : ℝ → G} {f' : G} {interval : Set ℝ} {t : ℝ}
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
        | (apply OdeDeriv.hasDerivWithinAt_smul_apply <;> ode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_mul_apply <;> ode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_inner_apply <;> ode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_fst <;> ode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_snd <;> ode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_apply <;> ode_deriv_step)
        | apply hasDerivWithinAt_const)

/--
`ode_deriv` proves a scalar `HasPrime` goal for an ordinary ODE. It automatically
unfolds the observable, proposed derivative, evolution domain, and vector field.
Use `ode_deriv [definitions]` to provide additional definitions or simplification
lemmas when necessary.
-/
syntax "ode_deriv" : tactic
syntax "ode_deriv" " [" term,* "]" : tactic

private def lastArg (args : Array Expr) (offset : Nat) : MetaM Expr :=
  if offset < args.size then
    pure args[args.size - 1 - offset]!
  else
    throwError "ode_deriv: malformed HasPrime goal"

private def addHeadDefinition (definitions : Array Name) (e : Expr) : Array Name :=
  match e.getAppFn.constName? with
  | some name => if definitions.contains name then definitions else definitions.push name
  | none => definitions

private def inferredDefinitions : TacticM (Array Name) := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  unless target.getAppFn.constName? == some ``HasPrime do
    throwError "ode_deriv: expected a HasPrime goal, got{indentExpr target}"
  let args := target.getAppArgs
  let semanticOde ← lastArg args 3
  let domain ← lastArg args 2
  let f ← lastArg args 1
  let fPrime ← lastArg args 0
  let ode ←
    if semanticOde.getAppFn.constName? == some ``Denotable.denotation then
      lastArg semanticOde.getAppArgs 0
    else
      pure semanticOde
  let definitions := addHeadDefinition #[] ode
  let definitions := addHeadDefinition definitions domain
  let definitions := addHeadDefinition definitions f
  return addHeadDefinition definitions fPrime

private def runOdeDeriv (definitions : Array (TSyntax `term)) : TacticM Unit := do
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
       | ode_deriv_step
       | (simp -failIfUnchanged
            [Function.comp_apply, inner_smul_right, inner_zero_left, $simpDefinitions,*] <;>
          ring_nf))))

elab_rules : tactic
  | `(tactic| ode_deriv) => runOdeDeriv #[]
  | `(tactic| ode_deriv [$definitions,*]) => runOdeDeriv definitions

end dLean
