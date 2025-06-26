/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import Lean.EnvExtension

namespace Lean

builtin_initialize metaExt : TagDeclarationExtension ← mkTagDeclarationExtension (asyncMode := .async)

/-- Marks in the environment extension that the given declaration has been declared by the user as `meta`. -/
def addMeta (env : Environment) (declName : Name) : Environment :=
  metaExt.tag env declName

/-- Returns true iff the user has declared the given declaration as `meta`. -/
def isMeta (env : Environment) (declName : Name) : Bool :=
  metaExt.isTagged env declName

/--
Returns the IR phases of the given declaration that should be considered accessible. Does not take
additional IR loaded for language server purposes into account.
-/
@[export lean_get_ir_phases]
def getIRPhases (env : Environment) (declName : Name) : IRPhases := Id.run do
  if !env.header.isModule then
    return .all
  match env.getModuleIdxFor? declName with
  | some idx => if isMeta env declName then .comptime else
    -- HACK: The old compiler gets the ABI wrong if the result is not an immediate
    -- constructor. The `match` can be removed once the new compiler is enabled.
    match env.header.modules[idx.toNat]?.map (·.irPhases) |>.get! with
    | .comptime => .comptime
    | .runtime => .runtime
    | .all => .all
  -- Allow `meta`->non-`meta` acesses in the same module
  | none => if isMeta env declName then .comptime else .all

end Lean
