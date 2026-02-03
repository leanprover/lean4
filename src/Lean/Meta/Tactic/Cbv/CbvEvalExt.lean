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

/--
A single entry in the `cbv_eval` extension.
Associates a target definition with a lemma providing a rewrite rule for it.
-/
structure CbvEvalEntry where
  /-- The definition we are registering a rewrite rule for. -/
  target : Name
  /-- The declaration name of the theorem providing the rewrite rule. -/
  declName  : Name
  deriving Inhabited, BEq, Hashable, Repr

/--
The persistent state of the `cbv_eval` extension.
Maps each target definition to the array of lemma names registered for it.
-/
structure CbvEvalState where
  /-- Map from target definition names to their registered rewrite lemmas. -/
  lemmas : NameMap (Array Name) := {}
  deriving Inhabited

/-- Insert a `CbvEvalEntry` into the state, appending to any existing lemmas for the target. -/
def CbvEvalState.addEntry (s : CbvEvalState) (e : CbvEvalEntry) : CbvEvalState :=
  let existing := (s.lemmas.find? e.target).getD #[]
  { s with lemmas := s.lemmas.insert e.target (existing.push e.declName) }

/-- The type of the `cbv_eval` environment extension. -/
abbrev CbvEvalExtension := SimpleScopedEnvExtension CbvEvalEntry CbvEvalState

/-- Initialize the `cbv_eval` extension. -/
builtin_initialize cbvEvalExt : CbvEvalExtension ←
  registerSimpleScopedEnvExtension {
    name     := `cbvEvalExt
    initial  := {}
    addEntry := CbvEvalState.addEntry
    exportEntry? := fun level entry => do
      guard (level == .private || !isPrivateName entry.target)
      return entry
  }

/--
Look up all lemma names registered for a given target definition
via the `cbv_eval` attribute.
Returns an empty array if no lemmas have been registered.
-/
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
    erase := fun lemmaName => do
      modifyEnv fun env => cbvEvalExt.modifyState env fun s =>
        { s with lemmas := s.lemmas.foldl (init := {}) fun acc target lemmas =>
            let filtered := lemmas.filter (· != lemmaName)
            if filtered.isEmpty then acc else acc.insert target filtered }
  }

end Lean.Meta.Tactic.Cbv
