/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module
prelude
public import Lean.Data.NameMap
public import Lean.ScopedEnvExtension
public import Lean.Elab.InfoTree
public import Lean.Meta.Sym.Simp.Theorems

public section
namespace Lean.Meta.Tactic.Cbv
open Lean.Meta.Sym.Simp

structure CbvEvalEntry where
  target : Name
  thm  : Theorem
  deriving BEq, Inhabited

def mkCbvTheoremFromConst (declName : Name) : MetaM (Name × Theorem) := do
  let cinfo ← getConstVal declName
  let us := cinfo.levelParams.map mkLevelParam
  let val := mkConst declName us
  let type ← inferType val
  unless (← isProp type) do
    throwError "Invalid `cbv` theorem"
  let fnName ← forallTelescope type fun _ body => do
    let some (_, lhs, _) := body.eq? | throwError "Equality expected"
    unless lhs.isApp do throwError "Application expected"
    let appFn := lhs.getAppFn
    let some constName := appFn.constName? | throwError "Not a constant application"
    return constName
  let thm ← mkTheoremFromDecl declName
  return (fnName, thm)

structure CbvEvalState where
  lemmas : NameMap Theorems := {}
  deriving Inhabited

def CbvEvalState.addEntry (s : CbvEvalState) (e : CbvEvalEntry) : CbvEvalState :=
  let existing := (s.lemmas.find? e.target).getD {}
  { s with lemmas := s.lemmas.insert e.target (existing.insert e.thm) }

abbrev CbvEvalExtension := SimpleScopedEnvExtension CbvEvalEntry CbvEvalState

builtin_initialize cbvEvalExt : CbvEvalExtension ←
  registerSimpleScopedEnvExtension {
    name     := `cbvEvalExt
    initial  := {}
    addEntry := CbvEvalState.addEntry
    exportEntry? := fun level entry => do
      guard (level == .private || !isPrivateName entry.target)
      return entry
  }

def getCbvEvalLemmas (target : Name) : CoreM (Option Theorems) := do
  let s := cbvEvalExt.getState (← getEnv)
  return (s.lemmas.find? target)

syntax (name := Parser.Attr.cbvEval) "cbv_eval" : attr

builtin_initialize
  registerBuiltinAttribute {
    ref   := `cbvEvalAttr
    name  := `cbv_eval
    descr := "Register a theorem as a rewrite rule for CBV evaluation of a given definition. \
              Usage: @[cbv_eval] theorem ..."
    applicationTime := AttributeApplicationTime.afterCompilation
    add   := fun lemmaName _ kind => do
      let ((targetName, thm), _) ← MetaM.run (mkCbvTheoremFromConst lemmaName) {}
      cbvEvalExt.add { target := targetName, thm := thm } kind
  }

end Lean.Meta.Tactic.Cbv
