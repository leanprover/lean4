/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.CompilerM
import Lean.Compiler.Decl

namespace Lean.Compiler

/-! Common Sub-expression Elimination -/

namespace CSE

structure State where
  map : Std.PHashMap Expr Expr := {}

abbrev M := StateRefT State CompilerM

mutual

partial def visitCases (casesInfo : CasesInfo) (cases : Expr) : M Expr := do
  let mut args := cases.getAppArgs
  for i in casesInfo.altsRange do
    args ← args.modifyM i visitLambda
  return mkAppN cases.getAppFn args

partial def visitLambda (e : Expr) : M Expr :=
  withNewScope do
    let (as, e) ← Compiler.visitLambda e
    let e ← mkLetUsingScope (← visitLet e)
    mkLambda as e

partial def visitLet (e : Expr) : M Expr := do
  let saved ← get
  try go e #[] finally set saved
where
  go (e : Expr) (xs : Array Expr) : M Expr := do
    match e with
    | .letE binderName type value body nonDep =>
      let mut value := value.instantiateRev xs
      if value.isLambda then
        value ← visitLambda value
      match (← get).map.find? value with
      | some x => go body (xs.push x)
      | none =>
        let type := type.instantiateRev xs
        let x ← mkLetDecl binderName type value nonDep
        unless isJpBinderName binderName do
          -- We currently don't eliminate common join points because we want to prevent
          -- jumps to out-of-scope join points.
          modify fun s => { s with map := s.map.insert value x }
        go body (xs.push x)
    | _ =>
      let e := e.instantiateRev xs
      if let some casesInfo ← isCasesApp? e then
        visitCases casesInfo e
      else
        return e

end

end CSE

/--
Common sub-expression elimination
-/
def Decl.cse (decl : Decl) : CoreM Decl :=
  decl.mapValue fun value => CSE.visitLambda value  |>.run' {}

end Lean.Compiler