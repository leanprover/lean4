/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Basic

namespace Lean.Meta

structure ElimAltInfo where
  name      : Name
  numFields : Nat

structure ElimInfo where
  name       : Name
  motivePos  : Nat
  targetsPos : Array Nat := #[]
  altsInfo   : Array ElimAltInfo := #[]

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

end Lean.Meta
