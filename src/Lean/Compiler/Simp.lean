/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.CompilerM
import Lean.Compiler.Decl
import Lean.Compiler.Stage1
import Lean.Compiler.InlineAttrs

namespace Lean.Compiler

namespace Simp

structure Config where
  increaseFactor : Nat := 2

structure Context where
  config : Config := {}
  jp? : Option Expr := none

structure State where
  unit : Unit := ()

abbrev SimpM := ReaderT Context $ StateRefT State CompilerM

def isInlineCandidate (e : Expr) : SimpM Bool := do
  let .const declName _ := e.getAppFn | return false
  unless hasInlineAttribute (← getEnv) declName do return false
  let some decl ← getStage1Decl? declName | return false
  return e.getAppNumArgs >= decl.getArity

partial def findExpr (e : Expr) : SimpM Expr := do
  match e with
  | .fvar fvarId =>
    let some (.ldecl (value := v) ..) ← findDecl? fvarId | return e
    findExpr v
  | .mdata _ e => findExpr e
  | _ => return e

mutual

partial def visitLambda (e : Expr) : SimpM Expr :=
  withNewScope do
    let (as, e) ← Compiler.visitLambda e
    let e ← mkLetUsingScope (← visitLet e)
    mkLambda as e

partial def visitCases (casesInfo : CasesInfo) (e : Expr) : SimpM Expr := do
  let mut args  := e.getAppArgs
  let major := args[casesInfo.discrsRange.stop - 1]!
  let major ← findExpr major
  if let some (ctorVal, ctorArgs) := major.constructorApp? (← getEnv) then
    /- Simplify `casesOn` constructor -/
    let ctorIdx := ctorVal.cidx
    let alt := args[casesInfo.altsRange.start + ctorIdx]!
    let ctorFields := ctorArgs[ctorVal.numParams:]
    let alt := alt.beta ctorFields
    assert! !alt.isLambda
    visitLet alt
  else
    for i in casesInfo.altsRange do
      args ← args.modifyM i visitLambda
    return mkAppN e.getAppFn args

partial def visitLet (e : Expr) : SimpM Expr := do
  go e #[]
where
  go (e : Expr) (xs : Array Expr) : SimpM Expr := do
    match e with
    | .letE binderName type value body nonDep =>
      let mut value := value.instantiateRev xs
      if value.isLambda then
        value ← visitLambda value
      let type := type.instantiateRev xs
      let x ← mkLetDecl binderName type value nonDep
      go body (xs.push x)
    | _ =>
      let e := e.instantiateRev xs
      if let some casesInfo ← isCasesApp? e then
        visitCases casesInfo e
      else match (← read).jp? with
        | none => return e
        | some jp => mkJump jp e

end

end Simp

def Decl.simp (decl : Decl) : CoreM Decl := do
  let decl ← decl.ensureUniqueLetVarNames
  /- TODO:
  - Collect local function number of occurrences.
  - Fixpoint.
  -/
  decl.mapValue fun value => Simp.visitLambda value |>.run {} |>.run' {}

end Lean.Compiler