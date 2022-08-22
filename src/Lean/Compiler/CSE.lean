/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.CompilerM
import Lean.Compiler.Decl
import Lean.Compiler.PExpr

namespace Lean.Compiler

/-! Common Sub-expression Elimination -/

namespace CSE

structure State where
  map : Std.PHashMap Expr Expr := {}

abbrev M := StateRefT State CompilerM

mutual

partial def visitLambda (xs : Array Expr) (e : Expr) : M PExpr :=
  PExpr.visitLambda xs e visitLet

partial def visitLet (xs : Array Expr) (e : Expr) : M (Array Expr × PExpr) := do
  let saved ← get
  try go xs e finally set saved
where
  go (xs : Array Expr) (e : Expr) : M (Array Expr × PExpr) := do
    match e with
    | .letE binderName type value body nonDep =>
      let value' ← if value.isLambda then
        (← visitLambda xs value).toExpr
      else
        pure <| value.instantiateRev xs
      if value'.isLambda then
        trace[Meta.debug] "nested lambda\n{value.instantiateRev xs}\n====>\n{value'}"
      let value := value'
      match (← get).map.find? value with
      | some x => go (xs.push x) body
      | none =>
        let type := type.instantiateRev xs
        let x ← mkLetDecl binderName type value nonDep
        unless isJpBinderName binderName do
          -- We currently don't eliminate common join points because we want to prevent
          -- jumps to out-of-scope join points.
          modify fun s => { s with map := s.map.insert value x }
        go (xs.push x) body
    | _ =>
      if let some casesInfo ← isCasesApp? e then
        return (xs, ← PExpr.visitCases xs casesInfo e visitLambda)
      else
        return (xs, e.instantiateRev xs)

end

end CSE

/--
Common sub-expression elimination
-/
def Decl.cse (decl : Decl) : CoreM Decl :=
  decl.mapValue fun value => do (← CSE.visitLambda #[] value  |>.run' {}).toExpr

end Lean.Compiler