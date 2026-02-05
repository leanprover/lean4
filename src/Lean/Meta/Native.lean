/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

module
prelude
public import Lean.Meta.Basic
import Lean.Util.CollectLevelParams
import Lean.AddDecl
import Lean.Meta.AppBuilder
import Lean.Elab.DeclarationRange

open Lean Meta

namespace Lean.Meta

/-!
This module contains infrastructure for proofs by native evaluation (`native decide`, `bv_decide`).
Such proofs involve a native computation using the Lean kernel, and then asserting the result
of that computation as an axiom towards the logic.
-/

public inductive NativeEqTrueResult where
  /-- The given expression `e` evalutes to true. `prf` is a proof of `e = true`. -/
  | success (prf : Expr)
  /-- The given expression `e` evalutes to false. -/
  | notTrue

/--
A call to `nativeEqTrue tacName e`, where `e` is a closed value of type `Bool`, will compile and run
that value, check that it evaluates to `true`, and if so, will add an axiom asserting `e = true` and
return that axiom.

It is the basis for `native_decide` and `bv_decide` tactics.
-/
public def nativeEqTrue (tacticName : Name) (e : Expr) (axiomDeclRange? : Option Syntax := none) : MetaM NativeEqTrueResult  := do
  let e ← instantiateMVars e
  if e.hasFVar then
    throwError m!"Tactic `{tacticName}` failed: Cannot native decide proposition with free variables:{indentExpr e}"
  if e.hasMVar then
    throwError m!"Tactic `{tacticName}` failed: Cannot native decide proposition with metavariables:{indentExpr e}"
  let levels := (collectLevelParams {} e).params.toList
  let isTrue ← withoutModifyingEnv do
    let auxDeclName ← mkAuxDeclName <| `_native ++ tacticName ++ `decl
    let decl := Declaration.defnDecl {
      name := auxDeclName
      levelParams := levels
      type := mkConst ``Bool
      value := e
      hints := .abbrev
      safety := .safe
    }
    try
      -- disable async codegen so we can catch its exceptions; we don't want to report `evalConst`
      -- failures below when the actual reason was a codegen failure
      withOptions (Elab.async.set · false) do
        addAndCompile (mayPostPoneCompile := false) decl
    catch ex =>
      throwError m!"Tactic `{tacticName}` failed. Error: {ex.toMessageData}"

    -- Now evaluate the constant, and check that it is true.
    try
      unsafe evalConst Bool auxDeclName
    catch ex =>
      throwError m!"\
        Tactic `{tacticName}` failed: Could not evaluate decidable instance. \
        Error: {ex.toMessageData}"

  unless isTrue do return .notTrue

  let auxAxiomName ← mkAuxDeclName <| `_native ++ tacticName ++ `ax
  let axDecl := Declaration.axiomDecl {
    name := auxAxiomName
    levelParams := levels
    type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) e (mkConst ``Bool.true)
    isUnsafe := false
  }
  addDecl axDecl
  if let some ref := axiomDeclRange? then
    Elab.addDeclarationRangesFromSyntax auxAxiomName ref

  let levelParams := levels.map mkLevelParam
  return .success <| mkConst auxAxiomName levelParams
