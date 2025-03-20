/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.Types
import Lean.Compiler.LCNF.InferType
import Lean.Compiler.LCNF.Simp.Basic

namespace Lean.Compiler.LCNF
namespace Simp

inductive CtorInfo where
  | ctor (val : ConstructorVal) (args : Array Arg)
  | /-- Natural numbers are morally constructor applications -/
    natVal (n : Nat)

def CtorInfo.getName : CtorInfo → Name
  | .ctor val _ => val.name
  | .natVal 0   => ``Nat.zero
  | .natVal _   => ``Nat.succ

def CtorInfo.getNumParams : CtorInfo → Nat
  | .ctor val _ => val.numParams
  | .natVal _ => 0

def CtorInfo.getNumFields : CtorInfo → Nat
  | .ctor val _ => val.numFields
  | .natVal 0   => 0
  | .natVal _   => 1

structure DiscrM.Context where
  /--
  A mapping from discriminant to constructor application it is equal to in the current context.
  -/
  discrCtorMap : FVarIdMap CtorInfo := {}
  /--
  A mapping from constructor application to discriminant it is equal to in the current context.
  -/
  ctorDiscrMap : PersistentExprMap FVarId := {}

/--
Helper monad for tracking mappings from discriminant to constructor applications and back.
The combinator `withDiscrCtor` should be used when visiting `cases` alternatives.
-/
abbrev DiscrM := ReaderT DiscrM.Context CompilerM

/--
If `fvarId` is a constructor application, returns constructor information.
Remark: we use the map `discrCtorMap`.
Remark: We use this method when simplifying projections and cases-constructor.
-/
def findCtor? (fvarId : FVarId) : DiscrM (Option CtorInfo) := do
  match (← findLetDecl? fvarId) with
  | some { value := .value (.natVal n), .. } =>
    return some <| .natVal n
  | some { value := .const declName _ args, .. } =>
    let some (.ctorInfo val) := (← getEnv).find? declName | return none
    return some <| .ctor val args
  | some _ => return none
  | none => return (← read).discrCtorMap.find? fvarId

def findCtorName? (fvarId : FVarId) : DiscrM (Option Name) := do
  let some ctorInfo ← findCtor? fvarId | return none
  return ctorInfo.getName

/--
If `type` is an inductive datatype, return its universe levels and parameters.
-/
def getIndInfo? (type : Expr) : CoreM (Option (List Level × Array Arg)) := do
  let type := type.headBeta
  let .const declName us := type.getAppFn | return none
  let .inductInfo info ← getConstInfo declName | return none
  unless type.getAppNumArgs >= info.numParams do return none
  let args := type.getAppArgs[:info.numParams].toArray.map fun
    | .fvar fvarId => .fvar fvarId
    | e => if e.isErased then .erased else .type e
  return some (us, args)

/--
Execute `x` with the information that `discr = ctorName ctorFields`.
We use this information to simplify nested cases on the same discriminant.
-/
@[inline] def withDiscrCtorImp (discr : FVarId) (ctorName : Name) (ctorFields : Array Param) (x : DiscrM α) : DiscrM α := do
  let ctx ← updateCtx
  withReader (fun _ => ctx) x
where
  updateCtx : DiscrM DiscrM.Context := do
    let ctorVal ← getConstInfoCtor ctorName
    let fieldArgs := ctorFields.map (Arg.fvar ·.fvarId)
    let ctx ← read
    if let some (us, params) ← getIndInfo? (← getType discr) then
      let ctorArgs := params ++ fieldArgs
      let ctorInfo := .ctor ctorVal ctorArgs
      let ctor := LetValue.const ctorVal.name us ctorArgs
      return { ctx with discrCtorMap := ctx.discrCtorMap.insert discr ctorInfo, ctorDiscrMap := ctx.ctorDiscrMap.insert ctor.toExpr discr }
    else
      -- For the discrCtor map, the constructor parameters are irrelevant for optimizations that use this information
      let ctorInfo := .ctor ctorVal (.replicate ctorVal.numParams Arg.erased ++ fieldArgs)
      return { ctx with discrCtorMap := ctx.discrCtorMap.insert discr ctorInfo }

@[inline, inherit_doc withDiscrCtorImp] def withDiscrCtor [MonadFunctorT DiscrM m] (discr : FVarId) (ctorName : Name) (ctorFields : Array Param) : m α → m α :=
  monadMap (m := DiscrM) <| withDiscrCtorImp discr ctorName ctorFields

def simpCtorDiscrCore? (e : Expr) : DiscrM (Option FVarId) := do
  let some discr := (← read).ctorDiscrMap.find? e | return none
  unless eqvTypes (← getType discr) (← inferType e) do return none
  return some <| discr

end Simp
end Lean.Compiler.LCNF
