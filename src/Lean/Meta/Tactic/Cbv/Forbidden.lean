/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Lean.ScopedEnvExtension

public section

namespace Lean.Meta.Tactic.Cbv

/-- An environment extension that tracks a set of forbidden names for CBV evaluation. -/
abbrev CbvForbiddenExtension := SimpleScopedEnvExtension Name (Std.HashSet Name)

/-- Initialize the `cbv_forbidden` attribute extension. -/
builtin_initialize cbvForbiddenExt : CbvForbiddenExtension ←
  registerSimpleScopedEnvExtension {
    name     := `cbvForbiddenExt
    initial  := {}
    addEntry := fun s n => s.insert n
  }

/-- Register the `cbv_forbidden` attribute. -/
builtin_initialize
  registerBuiltinAttribute {
    ref   := `cbvForbiddenAttr
    name  := `cbv_forbidden
    descr := "Mark declarations that should not be evaluated during CBV evaluation"
    applicationTime := AttributeApplicationTime.afterCompilation
    add   := fun declName _ kind =>
      cbvForbiddenExt.add declName kind
    erase := fun declName => do
      let s := cbvForbiddenExt.getState (← getEnv)
      modifyEnv fun env => cbvForbiddenExt.modifyState env fun _ => s.erase declName
  }

/-- Syntax for the `cbv_forbidden` attribute. -/
syntax (name := Parser.Attr.cbvForbidden) "cbv_forbidden" : attr

/-- Get the set of declarations marked with the `cbv_forbidden` attribute. -/
def cbvForbidden : CoreM (Std.HashSet Name) := do
  return cbvForbiddenExt.getState (← getEnv)

/-- Checks if thee given name is marked with the `cbv_forbidden` attribute. -/
def isForbidden (name : Name) : CoreM Bool := do
  return cbvForbiddenExt.getState (← getEnv) |>.contains name

end Lean.Meta.Tactic.Cbv
