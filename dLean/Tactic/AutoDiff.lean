import dLean.Tactic.OdeDeriv
import Mathlib.Lean.Meta.Simp

/-!
# Automatic Differentiation

This module provides `autodiff`, a tactic that computes the Lie derivative of
a scalar observable along an autonomous ODE and proves the resulting
`HasPrime` goal using `ode_deriv`.
-/

namespace dLean
open Lean Meta Elab Tactic

namespace AutoDiff

private structure Coordinate where
  stateVar : Expr
  tangent : Expr

private def mkRealNat (n : Nat) : MetaM Expr := do
  let real := mkConst ``Real
  let numeral := mkNatLit n
  let instanceType := mkApp2 (mkConst ``OfNat [0]) real numeral
  let inst ← synthInstance instanceType
  pure <| mkApp3 (mkConst ``OfNat.ofNat [0]) real numeral inst

private def mkZero (e : Expr) : MetaM Expr := do
  let type ← inferType e
  let level ← mkFreshLevelMVar
  let inst ← synthInstance (mkApp (mkConst ``Zero [level]) type)
  pure <| mkApp2 (mkConst ``Zero.zero [level]) type inst

private def dependsOn (coordinates : Array Coordinate) (e : Expr) : Bool :=
  coordinates.any fun coordinate => e.containsFVar coordinate.stateVar.fvarId!

private def lastArg (args : Array Expr) (offset : Nat) : MetaM Expr :=
  if offset < args.size then
    pure args[args.size - 1 - offset]!
  else
    throwError "autodiff: malformed application"

private def add (left right : Expr) : MetaM Expr :=
  mkAppM ``HAdd.hAdd #[left, right]

private def sub (left right : Expr) : MetaM Expr :=
  mkAppM ``HSub.hSub #[left, right]

private def mul (left right : Expr) : MetaM Expr :=
  mkAppM ``HMul.hMul #[left, right]

private def smul (scalar vector : Expr) : MetaM Expr :=
  mkAppM ``HSMul.hSMul #[scalar, vector]

private def inner (left right : Expr) : MetaM Expr :=
  return (← simpOnlyNames [``inner_smul_right, ``inner_zero_left, ``inner_zero_right]
    (← mkAppM ``inner #[mkConst ``Real, left, right])).expr

private partial def powDerivative
    (base dbase : Expr) : Nat → MetaM Expr
  | 0 => mkRealNat 0
  | 1 => pure dbase
  | n + 2 => do
      let exponent := n + 1
      let previous ← mkAppM ``HPow.hPow #[base, mkNatLit exponent]
      add (← mul (← powDerivative base dbase exponent) base) (← mul previous dbase)

private partial def differentiate
    (coordinates : Array Coordinate) (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if !dependsOn coordinates e then
    return ← mkZero e

  if let some coordinate := coordinates.find? fun coordinate =>
      coordinate.stateVar == e then
    return coordinate.tangent

  let fn := e.getAppFn
  let args := e.getAppArgs
  if (fn.constName?.map (·.toString.endsWith ".Real.add")).getD false then
    let left ← lastArg args 1
    let right ← lastArg args 0
    return ← match dependsOn coordinates left, dependsOn coordinates right with
      | true, true => add (← differentiate coordinates left) (← differentiate coordinates right)
      | true, false => differentiate coordinates left
      | false, true => differentiate coordinates right
      | false, false => mkZero e
  if (fn.constName?.map (·.toString.endsWith "inner")).getD false then
    let left ← lastArg args 1
    let right ← lastArg args 0
    return ← match dependsOn coordinates left, dependsOn coordinates right with
      | true, true =>
          add
            (← inner left (← differentiate coordinates right))
            (← inner (← differentiate coordinates left) right)
      | true, false => inner (← differentiate coordinates left) right
      | false, true => inner left (← differentiate coordinates right)
      | false, false => mkZero e
  match fn.constName? with
  | some ``HAdd.hAdd =>
      let left ← lastArg args 1
      let right ← lastArg args 0
      match dependsOn coordinates left, dependsOn coordinates right with
      | true, true => add (← differentiate coordinates left) (← differentiate coordinates right)
      | true, false => differentiate coordinates left
      | false, true => differentiate coordinates right
      | false, false => mkZero e
  | some ``HSub.hSub =>
      let left ← lastArg args 1
      let right ← lastArg args 0
      match dependsOn coordinates left, dependsOn coordinates right with
      | true, true => sub (← differentiate coordinates left) (← differentiate coordinates right)
      | true, false => differentiate coordinates left
      | false, true => mkAppM ``Neg.neg #[← differentiate coordinates right]
      | false, false => mkZero e
  | some ``HMul.hMul =>
      let left ← lastArg args 1
      let right ← lastArg args 0
      match dependsOn coordinates left, dependsOn coordinates right with
      | true, true =>
          add
            (← mul (← differentiate coordinates left) right)
            (← mul left (← differentiate coordinates right))
      | true, false => mul (← differentiate coordinates left) right
      | false, true => mul left (← differentiate coordinates right)
      | false, false => mkZero e
  | some ``HSMul.hSMul =>
      let scalar ← lastArg args 1
      let vector ← lastArg args 0
      match dependsOn coordinates scalar, dependsOn coordinates vector with
      | true, true =>
          add
            (← smul scalar (← differentiate coordinates vector))
            (← smul (← differentiate coordinates scalar) vector)
      | true, false => smul (← differentiate coordinates scalar) vector
      | false, true => smul scalar (← differentiate coordinates vector)
      | false, false => mkZero e
  | some ``Neg.neg =>
      mkAppM ``Neg.neg #[← differentiate coordinates (← lastArg args 0)]
  | some ``HPow.hPow =>
      let base ← lastArg args 1
      let exponent ← whnf (← lastArg args 0)
      let .lit (.natVal n) := exponent |
        throwError "autodiff: only powers with a literal natural exponent are supported"
      powDerivative base (← differentiate coordinates base) n
  | some ``Real.sin =>
      let argument ← lastArg args 0
      mul (← mkAppM ``Real.cos #[argument]) (← differentiate coordinates argument)
  | some ``Real.cos =>
      let argument ← lastArg args 0
      let sine ← mkAppM ``Real.sin #[argument]
      mul (← mkAppM ``Neg.neg #[sine])
        (← differentiate coordinates argument)
  | _ =>
      throwError
        "autodiff: unsupported state-dependent expression{indentExpr e}\n\
         Supported operations are +, -, *, scalar multiplication, inner products,\n\
         negation, natural powers, sin, and cos."

private def headDefinition? (e : Expr) : Option Name :=
  e.getAppFn.constName?.filter fun name =>
    name != ``id && name != ``Function.comp

private partial def normalizeRealOperations (e : Expr) : MetaM Expr := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  let normalizedArgs ← args.mapM normalizeRealOperations
  let normalized := mkAppN fn normalizedArgs
  match fn.constName? with
  | some name =>
      if name.toString.endsWith ".Real.add" then
        add (← lastArg normalizedArgs 1) (← lastArg normalizedArgs 0)
      else if name.toString.endsWith ".Real.mul" then
        mul (← lastArg normalizedArgs 1) (← lastArg normalizedArgs 0)
      else
        pure normalized
  | none => pure normalized

private def simplifyDefinition (definition : Expr) (e : Expr) : MetaM Expr := do
  match headDefinition? definition with
  | some _ =>
      let some unfolded ← unfoldDefinition? e (ignoreTransparency := true) |
        throwError "autodiff: could not unfold{indentExpr e}"
      normalizeRealOperations (← simpOnlyNames [] unfolded).expr
  | none => normalizeRealOperations (← simpOnlyNames [] e).expr

private def symbolicDerivative (vectorField f : Expr) : MetaM Expr := do
  let fType ← whnf (← inferType f)
  let .forallE _ stateType resultType _ := fType |
    throwError "autodiff: expected a scalar state function, got{indentExpr fType}"
  unless ← isDefEq resultType (mkConst ``Real) do
    throwError "autodiff: expected a function returning Real, got{indentExpr resultType}"

  let stateTypeWhnf ← whnf stateType
  if stateTypeWhnf.isAppOfArity ``Prod 2 then
    let #[leftType, rightType] := stateTypeWhnf.getAppArgs |
      throwError "autodiff: malformed product state type"
    withLocalDeclD `x leftType fun x =>
      withLocalDeclD `v rightType fun v => do
        let state ← mkAppM ``Prod.mk #[x, v]
        let fBody ← simplifyDefinition f (mkApp f state)
        let odeBody ← simplifyDefinition vectorField (mkApp vectorField state)
        unless odeBody.isAppOfArity ``Prod.mk 4 do
          throwError "autodiff: the vector field did not reduce to a product{indentExpr odeBody}"
        let odeArgs := odeBody.getAppArgs
        let dx ← lastArg odeArgs 1
        let dv ← lastArg odeArgs 0
        let body ← differentiate #[⟨x, dx⟩, ⟨v, dv⟩] fBody
        let coordinateFunction ← mkLambdaFVars #[x, v] body
        withLocalDeclD `st stateType fun st => do
          let sx ← mkAppM ``Prod.fst #[st]
          let sv ← mkAppM ``Prod.snd #[st]
          mkLambdaFVars #[st] (mkAppN coordinateFunction #[sx, sv]).headBeta
  else
    withLocalDeclD `st stateType fun st => do
      let tangent ← simplifyDefinition vectorField (mkApp vectorField st)
      let body ← simplifyDefinition f (mkApp f st)
      mkLambdaFVars #[st] (← differentiate #[⟨st, tangent⟩] body)

private def autonomousVectorField (semanticOde : Expr) : MetaM Expr := do
  let semanticOde ← instantiateMVars semanticOde
  unless semanticOde.getAppFn.constName? == some ``Denotable.denotation do
    throwError "autodiff: expected an ODE obtained through Denotable.denotation"
  let args := semanticOde.getAppArgs
  let vectorField ← lastArg args 0
  let vectorFieldType ← whnf (← inferType vectorField)
  let .forallE _ stateType resultType _ := vectorFieldType |
    throwError "autodiff: expected an autonomous vector field"
  unless ← isDefEq stateType resultType do
    throwError "autodiff: time-dependent vector fields are not yet supported"
  pure vectorField

private def runOdeDeriv : TacticM Unit := do
  evalTactic (← `(tactic| ode_deriv))

/--
`autodiff` computes and assigns `?f'` in a `HasPrime ode domain f ?f'` goal,
then proves the resulting derivative equation using `ode_deriv`.

It supports autonomous vector-field ODEs and scalar expressions built from
addition, subtraction, multiplication, scalar multiplication, inner products,
negation, natural powers, sine, and cosine. If the derivative is already
supplied, `autodiff` instead applies `ode_deriv` directly.
-/
elab "autodiff" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  unless target.getAppFn.constName? == some ``HasPrime do
    throwError "autodiff: expected a HasPrime goal, got{indentExpr target}"
  let args := target.getAppArgs
  let semanticOde ← lastArg args 3
  let f ← lastArg args 1
  let fPrime ← lastArg args 0
  match fPrime with
  | .mvar fPrimeGoal =>
      let vectorField ← autonomousVectorField semanticOde
      let derivative ← symbolicDerivative vectorField f
      fPrimeGoal.assign derivative
      runOdeDeriv
  | _ => runOdeDeriv

end AutoDiff
end dLean
