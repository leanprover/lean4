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

public section
namespace Lean.Meta.Tactic.Cbv


structure CbvEvalEntry where
  /-- The definition we are registering a rewrite rule for. -/
  target : Name
  /-- The declaration name of the theorem providing the rewrite rule. -/
  declName  : Name
  deriving Inhabited, BEq, Hashable, Repr

structure CbvEvalState where
  lemmas : NameMap (Array Name) := {}
  deriving Inhabited

def CbvEvalState.addEntry (s : CbvEvalState) (e : CbvEvalEntry) : CbvEvalState :=
  let existing := (s.lemmas.find? e.target).getD #[]
  { s with lemmas := s.lemmas.insert e.target (existing.push e.declName) }

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

def getCbvEvalLemmas (target : Name) : CoreM (Option <| Array Name) := do
  trace[Meta.Tactic.cbv] "trying to get user lemmas for: {target}"
  let s := cbvEvalExt.getState (← getEnv)
  return (s.lemmas.find? target)

/-- Syntax for the `cbv_eval` attribute. -/
syntax (name := Parser.Attr.cbvEval) "cbv_eval " ident : attr

/-- Register the `cbv_eval` attribute. -/
builtin_initialize
  registerBuiltinAttribute {
    ref   := `cbvEvalAttr
    name  := `cbv_eval
    descr := "Register a theorem as a rewrite rule for CBV evaluation of a given definition. \
              Usage: @[cbv_eval targetDef] theorem ..."
    applicationTime := AttributeApplicationTime.afterCompilation
    add   := fun lemmaName stx kind => do
      let fnNameStx ← Attribute.Builtin.getIdent <| stx
      let targetName ← Elab.realizeGlobalConstNoOverloadWithInfo fnNameStx
      cbvEvalExt.add { target := targetName, declName := lemmaName } kind
  }

end Lean.Meta.Tactic.Cbv
