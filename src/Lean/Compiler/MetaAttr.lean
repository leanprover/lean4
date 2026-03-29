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

/-- Marks in the environment extension that the given declaration has been declared by the user as `meta`. -/
def markMeta (env : Environment) (declName : Name) : Environment :=
  metaExt.tag env declName

/-- Returns true iff the user has declared the given declaration as `meta`. -/
def isMarkedMeta (env : Environment) (declName : Name) : Bool :=
  metaExt.isTagged env declName

/--
Set of IR decls that should be made available to any importer. This is a superset of `metaExt`
(except for non-defs such as `meta structure`), which is managed by the elaborator and has a
different async mode. More precisely, it contains the closure of `metaExt` as well as further
derived decls such as `_boxed` versions. We store this set primarily to filter exports in
`declMapExt`; we persist it in `.olean.private` for the benefit of `shake`.
-/
private builtin_initialize declMetaExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun _ => {}
    addEntryFn := fun s n => s.insert n
    asyncMode := .sync
    replay? := some <| SimplePersistentEnvExtension.replayOfFilter (!·.contains ·) (·.insert ·)
    exportEntriesFnEx? := some fun env s entries =>
      let decls := entries.foldl (init := #[]) fun decls decl => decls.push decl
      { exported := #[], server := #[], «private» := decls.qsort Name.quickLt }
  }

/-- Whether a declaration should be exported for interpretation. -/
def isDeclMeta (env : Environment) (declName : Name) : Bool :=
  if !env.header.isModule then
    true
  else
    -- The interpreter may call the boxed variant even if the IR does not directly reference it, so
    -- use same visibility as base decl.
    -- Note that boxed decls are created after the `inferVisibility` pass.
    let inferFor := match declName with
      | .str n "_boxed" => n
      | n               => n
    match env.getModuleIdxFor? declName with
    | some idx => declMetaExt.getModuleEntries env idx |>.binSearchContains inferFor Name.quickLt
    | none => declMetaExt.getState env |>.contains inferFor

/-- Marks a declaration to be exported for interpretation. -/
def setDeclMeta (env : Environment) (declName : Name) : Environment :=
  if isDeclMeta env declName then
    env
  else
    declMetaExt.addEntry env declName

/--
Returns the IR phases of the given declaration that should be considered accessible. Does not take
additional IR loaded for language server purposes into account.
-/
def getIRPhases (env : Environment) (declName : Name) : IRPhases := Id.run do
  if !env.header.isModule then
    return .all
  match env.getModuleIdxFor? declName with
  | some idx =>
    if isMarkedMeta env declName then
      .comptime
    else
      env.header.modules[idx]?.map (·.irPhases) |>.get!
  | none =>
    if env.find? declName |>.all (·.isCtor) then
      -- Do not check ctors (trivial) or decls not in env (compiler-generated)
      .all
    else if isMarkedMeta env declName then
      .comptime
    else
      .runtime

end Lean
