module

prelude
public import Lean.Meta.Basic
import Lean.Meta.WHNF
import Lean.Structure
import Lean.ProjFns

public section

namespace Lean.Meta.Tactic.Reparametrize

/--
The constructor or the projection of a one-field structure with concrete parameters.
`ctor` and `proj` are definitionally mutually inverse functions.
-/
structure Bijection where
  isCtor : Bool
  ctorVal : ConstructorVal
  us : List Level
  params : Array Expr

def Bijection.inv (b : Bijection) : Bijection :=
  { b with isCtor := !b.isCtor }

protected def Bijection.mkApp (b : Bijection) (e : Expr) : MetaM Expr :=
  -- TODO: cancellation of inverses
  if b.isCtor then
    return mkApp (mkAppN (mkConst b.ctorVal.name b.us) b.params) e
  else
    mkProjFn b.ctorVal b.us b.params 0 e

private def buildBijection? (isCtor : Bool) (structName : Name) (us : List Level)
    (params : Array Expr) :
    MetaM (Option Bijection) := do
  let env ← getEnv
  let some ctorVal := getNonRecStructureCtor? env structName | return none
  if ctorVal.numFields ≠ 1 then return none
  return some { isCtor, ctorVal, us, params }

-- /-- The constructor and the projection of the one-field structure `structName` with universes `us`
-- and parameters `params`. -/
-- private def structCtorProj? (structName : Name) (us : List Level) (params : Array Expr) :
--     MetaM (Option (Expr × Expr)) := do
--   let env ← getEnv
--   let some (.inductInfo { isRec := false, ctors := [ctorName], numIndices := 0, numParams, .. }) :=
--     env.find? structName | return none
--   let some info := getStructureInfo? env structName | return none
--   let #[fieldName] := info.fieldNames | return none
--   let some projFn := getProjFnForField? env structName fieldName | return none
--   unless params.size == numParams do return none
--   return some (mkAppN (mkConst ctorName us) params, mkAppN (mkConst projFn us) params)


/-
PREVIOUSLY:

* returned none on bare fvars
-/

structure BijectionWrappedFVar where
  fvarId : FVarId
  bijectionsInsideOut : List Bijection

/--
Returns `some (x, [b₁, …, bₙ])` if `e` is `bₙ (… (b₁ x) …)` for a free variable `x` and
bijections `bᵢ`, `n ≥ 1`.
-/
partial def bijectionWrappedFVar? (e : Expr) (outer : List Bijection := []) :
    MetaM (Option BijectionWrappedFVar) := do
  let e := e.consumeMData
  match e with
  | .fvar x =>
    return some ⟨x, outer⟩
  | .proj structName 0 x =>
    let xType ← whnfD (← inferType x)
    let .const _ us := xType.getAppFn | return none
    let some b ← buildBijection? (isCtor := false) structName us xType.getAppArgs
      | return none
    bijectionWrappedFVar? x (b :: outer)
  | .app .. =>
    let .const declName us := e.getAppFn | return none
    let args := e.getAppArgs
    let env ← getEnv
    if let some projInfo := env.getProjectionFnInfo? declName then
      let some ctorVal ← isCtor? projInfo.ctorName | return none
      if args.size ≠ ctorVal.numParams + 1 then return none
      let params := args.extract 0 ctorVal.numParams
      let x := args[ctorVal.numParams]!
      let some b ← buildBijection? (isCtor := false) ctorVal.induct us params
        | return none
      bijectionWrappedFVar? x (b :: outer)
    else if let some ctorVal ← isCtor? declName then
      if args.size ≠ ctorVal.numParams + 1 then return none
      let params := args.extract 0 ctorVal.numParams
      let x := args[ctorVal.numParams]!
      let some b ← buildBijection? (isCtor := true) ctorVal.induct us params
        | return none
      bijectionWrappedFVar? x (b :: outer)
    else
      return none
  | _ =>
    return none

end Lean.Meta.Tactic.Reparametrize
