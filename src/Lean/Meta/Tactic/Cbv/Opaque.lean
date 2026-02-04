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

abbrev CbvOpaqueExtension := SimpleScopedEnvExtension Name (Std.HashSet Name)

builtin_initialize cbvOpaqueExt : CbvOpaqueExtension ←
  registerSimpleScopedEnvExtension {
    name     := `cbvOpaqueExt
    initial  := {}
    addEntry := fun s n => s.insert n
  }

builtin_initialize
  registerBuiltinAttribute {
    ref   := `cbvOpaqueAttr
    name  := `cbv_opaque
    descr := "Mark declarations that should not be unfolded by the `cbv` tactic"
    applicationTime := AttributeApplicationTime.afterCompilation
    add   := fun declName _ kind =>
      cbvOpaqueExt.add declName kind
    erase := fun declName => do
      let s := cbvOpaqueExt.getState (← getEnv)
      modifyEnv fun env => cbvOpaqueExt.modifyState env fun _ => s.erase declName
  }

def cbvOpaque : CoreM (Std.HashSet Name) := do
  return cbvOpaqueExt.getState (← getEnv)

def isCbvOpaque (name : Name) : CoreM Bool := do
  return cbvOpaqueExt.getState (← getEnv) |>.contains name

end Lean.Meta.Tactic.Cbv
