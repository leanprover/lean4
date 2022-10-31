/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.Types
import Lean.Compiler.LCNF.InferType
import Lean.Compiler.LCNF.Simp.Basic

set_option warningAsError false
#exit

namespace Lean.Compiler.LCNF
namespace Simp

structure DiscrM.Context where
  /--
  A mapping from discriminant to constructor application it is equal to in the current context.
  -/
  discrCtorMap : FVarIdMap Expr := {}
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
This method uses `findExpr`, and if the result is a free variable, checks whether it is in the map `discrCtorMap`.
We use this method when simplifying projections and cases-constructor.
-/
def findCtormer (e : Expr) : DiscrM Expr := do
  let e ← findExpr e
  let .fvar fvarId := e | return e
  let some ctor := (← read).discrCtorMap.find? fvarId | return e
  return ctor

/--
If `type` is an inductive datatype, return its universe levels and parameters.
-/
def getIndInfo? (type : Expr) : CoreM (Option (List Level × Array Expr)) := do
  let type := type.headBeta
  let .const declName us := type.getAppFn | return none
  let .inductInfo info ← getConstInfo declName | return none
  unless type.getAppNumArgs >= info.numParams do return none
  return some (us, type.getAppArgs[:info.numParams])

/--
Execute `x` with the information that `discr = ctorName ctorFields`.
We use this information to simplify nested cases on the same discriminant.
-/
@[inline] def withDiscrCtorImp (discr : FVarId) (ctorName : Name) (ctorFields : Array Param) (x : DiscrM α) : DiscrM α := do
  let ctx ← updateCtx
  withReader (fun _ => ctx) x
where
  updateCtx : DiscrM DiscrM.Context := do
    let ctorInfo ← getConstInfoCtor ctorName
    let fieldArgs := ctorFields.map (.fvar ·.fvarId)
    let ctx ← read
    if let some (us, params) ← getIndInfo? (← getType discr) then
      let ctor := mkAppN (mkAppN (mkConst ctorName us) params) fieldArgs
      return { ctx with discrCtorMap := ctx.discrCtorMap.insert discr ctor, ctorDiscrMap := ctx.ctorDiscrMap.insert ctor discr }
    else
      -- For the discrCtor map, the constructor parameters are irrelevant for optimizations that use this information
      let ctor := mkAppN (mkAppN (mkConst ctorName) (mkArray ctorInfo.numParams erasedExpr)) fieldArgs
      return { ctx with discrCtorMap := ctx.discrCtorMap.insert discr ctor }

@[inline, inherit_doc withDiscrCtorImp] def withDiscrCtor [MonadFunctorT DiscrM m] (discr : FVarId) (ctorName : Name) (ctorFields : Array Param) : m α → m α :=
  monadMap (m := DiscrM) <| withDiscrCtorImp discr ctorName ctorFields

def simpCtorDiscrCore? (e : Expr) : DiscrM (Option Expr) := do
  let some discr := (← read).ctorDiscrMap.find? e | return none
  unless eqvTypes (← getType discr) (← inferType e) do return none
  return some <| .fvar discr

end Simp
end Lean.Compiler.LCNF
