/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Lean.EnvExtension

public section

namespace Lean

/-- Environment extension collecting `meta` annotations. -/
private builtin_initialize metaExt : TagDeclarationExtension ←
  -- set by `addPreDefinitions`; if we ever make `def` elaboration async, it should be moved to
  -- remain on the main environment branch
  mkTagDeclarationExtension (asyncMode := .async .mainEnv)
/--
Environment extension collecting declarations *could* have been marked as `meta` by the user but
were not, so should not allow access to `meta` declarations to surface phase distinction errors as
soon as possible.
-/
private builtin_initialize notMetaExt : EnvExtension NameSet ←
  registerEnvExtension
    (mkInitial := pure {})
    (asyncMode := .async .mainEnv)
    (replay? := some fun _ _ newEntries s => newEntries.foldl (·.insert) s)

/-- Marks in the environment extension that the given declaration has been declared by the user as `meta`. -/
def addMeta (env : Environment) (declName : Name) : Environment :=
  metaExt.tag env declName

/--
Marks the given declaration as not being annotated with `meta` even if it could have been by the
user.
-/
def addNotMeta (env : Environment) (declName : Name) : Environment :=
  notMetaExt.modifyState (asyncDecl := declName) env (·.insert declName)

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
  | some idx =>
    if isMeta env declName then
      .comptime
    else
      env.header.modules[idx.toNat]?.map (·.irPhases) |>.get!
  | none =>
    if isMeta env declName then
      .comptime
    else if notMetaExt.getState env |>.contains declName then
      .runtime
    else
      -- Allow `meta`->non-`meta` references in the same module for auxiliary declarations the user
      -- could not have marked as `meta` themselves.
      .all

end Lean
