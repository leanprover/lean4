/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module
prelude
public import Lean.Data.NameMap
public import Lean.ScopedEnvExtension

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
  }

/--
Look up all lemma names registered for a given target definition
via the `cbv_eval` attribute.
Returns an empty array if no lemmas have been registered.
-/
def getCbvEvalLemmas (target : Name) : CoreM (Array Name) := do
  let s := cbvEvalExt.getState (← getEnv)
  return (s.lemmas.find? target).getD #[]

end Lean.Meta.Tactic.Cbv
