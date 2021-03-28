/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Basic
import Lean.Meta.Check

namespace Lean.Meta

structure ElimAltInfo where
  name      : Name
  numFields : Nat
  deriving Repr

structure ElimInfo where
  name       : Name
  motivePos  : Nat
  targetsPos : Array Nat := #[]
  altsInfo   : Array ElimAltInfo := #[]
  deriving Repr

def getElimInfo (declName : Name) : MetaM ElimInfo := do
  let declInfo ← getConstInfo declName
  forallTelescopeReducing declInfo.type fun xs type => do
    let motive  := type.getAppFn
    let targets := type.getAppArgs
    unless motive.isFVar && targets.all (·.isFVar) && targets.size > 0 do
      throwError "unexpected eliminator resulting type{indentExpr type}"
    let motiveType ← inferType motive
    forallTelescopeReducing motiveType fun motiveArgs motiveResultType => do
      unless motiveArgs.size == targets.size do
        throwError "unexpected number of arguments at motive type{indentExpr motiveType}"
      unless motiveResultType.isSort do
        throwError "motive result type must be a sort{indentExpr motiveType}"
    let some motivePos ← pure (xs.indexOf? motive) |
      throwError "unexpected eliminator type{indentExpr declInfo.type}"
    let targetsPos ← targets.mapM fun target => do
      match xs.indexOf? target with
      | none => throwError "unexpected eliminator type{indentExpr declInfo.type}"
      | some targetPos => pure targetPos.val
    let mut altsInfo := #[]
    for i in [:xs.size] do
      let x := xs[i]
      if x != motive && !targets.contains x then
        let xDecl ← getLocalDecl x.fvarId!
        if xDecl.binderInfo.isExplicit then
          let numFields ← forallTelescopeReducing xDecl.type fun args _ => pure args.size
          altsInfo := altsInfo.push { name := xDecl.userName, numFields := numFields : ElimAltInfo }
    pure { name := declName, motivePos := motivePos, targetsPos := targetsPos, altsInfo := altsInfo }

/--
  Eliminators/recursors may have implicit targets. For builtin recursors, all indices are implicit targets.
  Given an eliminator and the sequence of explicit targets, this methods returns a new sequence containing
  implicit and explicit targets.
-/
partial def addImplicitTargets (elimInfo : ElimInfo) (targets : Array Expr) : MetaM (Array Expr) :=
  withNewMCtxDepth do
    let f ← mkConstWithFreshMVarLevels elimInfo.name
    let targets ← collect (← inferType f) 0 0 #[]
    let targets ← targets.mapM instantiateMVars
    for target in targets do
      if (← hasAssignableMVar target) then
        throwError "failed to infer implicit target, it contains unresolved metavariables{indentExpr target}"
    return targets
where
  collect (type : Expr) (argIdx targetIdx : Nat) (targets' : Array Expr) : MetaM (Array Expr) := do
    match (← whnfD type) with
    | Expr.forallE _ d b c =>
      if elimInfo.targetsPos.contains argIdx then
        if c.binderInfo.isExplicit then
          unless targetIdx < targets.size do
            throwError "insufficient number of targets for '{elimInfo.name}'"
          let target := targets[targetIdx]
          let targetType ← inferType target
          unless (← isDefEq d targetType) do
            throwError "target{indentExpr target}\n{← mkHasTypeButIsExpectedMsg targetType d}"
          collect (b.instantiate1 target) (argIdx+1) (targetIdx+1) (targets'.push target)
        else
          let implicitTarget ← mkFreshExprMVar d
          collect (b.instantiate1 implicitTarget) (argIdx+1) targetIdx (targets'.push implicitTarget)
      else
        collect (b.instantiate1 (← mkFreshExprMVar d)) (argIdx+1) targetIdx targets'
    | _ =>
      return targets'

end Lean.Meta
