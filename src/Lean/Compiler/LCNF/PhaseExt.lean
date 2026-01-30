/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.LCNF.PassManager

public section

namespace Lean.Compiler.LCNF

/-- Creates a replayable local environment extension holding a name set. -/
private def mkDeclSetExt : IO (EnvExtension (List Name × NameSet)) :=
  registerEnvExtension
    (mkInitial := pure ([], {}))
    (asyncMode := .sync)
    (replay? := some <| fun oldState newState _ s =>
      let newEntries := newState.1.take (newState.1.length - oldState.1.length)
      newEntries.foldl (init := s) fun s n =>
        if s.1.contains n then
          s
        else
          (n :: s.1, if newState.2.contains n then s.2.insert n else s.2))

/--
Set of declarations to be exported to other modules; visibility shared by base/mono/IR phases.
-/
private builtin_initialize publicDeclsExt : EnvExtension (List Name × NameSet) ← mkDeclSetExt

-- The following extensions are per-phase as e.g. a declaration may be inlineable in the mono phase
-- because it directly unfolds to a `_redArg` call, but making its body in the base phase available
-- as well may lead to opportunistic inlining there, exposing references to declarations that we did
-- not export, leading to compilation errors. Ensuring those declarations are exported as well would
-- be possible, but would mean more information than intended is exported, potentially leading to
-- surprising rebuilds.

/--
Set of public declarations whose base bodies should be exported to other modules
-/
private builtin_initialize baseTransparentDeclsExt : EnvExtension (List Name × NameSet) ← mkDeclSetExt
/--
Set of public declarations whose mono bodies should be exported to other modules
-/
private builtin_initialize monoTransparentDeclsExt : EnvExtension (List Name × NameSet) ← mkDeclSetExt
/--
Set of public declarations whose impure bodies should be exported to other modules
-/
private builtin_initialize impureTransparentDeclsExt : EnvExtension (List Name × NameSet) ← mkDeclSetExt

private def getTransparencyExt : Phase → EnvExtension (List Name × NameSet)
  | .base => baseTransparentDeclsExt
  | .mono => monoTransparentDeclsExt
  | .impure => impureTransparentDeclsExt

def isDeclPublic (env : Environment) (declName : Name) : Bool := Id.run do
  if !env.header.isModule then
    return true
  -- The IR compiler may call the boxed variant it introduces after we do visibility inference, so
  -- use same visibility as base decl.
  let inferFor := match declName with
    | .str n "_boxed" => n
    | n               => n
  let (_, map) := publicDeclsExt.getState env
  map.contains inferFor

def setDeclPublic (env : Environment) (declName : Name) : Environment :=
  if isDeclPublic env declName then
    env
  else
    publicDeclsExt.modifyState env fun s =>
      (declName :: s.1, s.2.insert declName)

def isDeclTransparent (env : Environment) (phase : Phase) (declName : Name) : Bool := Id.run do
  if !env.header.isModule then
    return true
  let (_, map) := getTransparencyExt phase |>.getState env
  map.contains declName

def setDeclTransparent (env : Environment) (phase : Phase) (declName : Name) : Environment :=
  if isDeclTransparent env phase declName then
    env
  else
    getTransparencyExt phase |>.modifyState env fun s =>
      (declName :: s.1, s.2.insert declName)

abbrev DeclExtState (pu : Purity) := PHashMap Name (Decl pu)

private abbrev declLt (a b : Decl pu) :=
  Name.quickLt a.name b.name

private def sortedDecls (s : DeclExtState pu) : Array (Decl pu) :=
  let decls := s.foldl (init := #[]) fun ps _ v => ps.push v
  decls.qsort declLt

private abbrev findAtSorted? (decls : Array (Decl pu)) (declName : Name) : Option (Decl pu) :=
  let tmpDecl : Decl pu := default
  let tmpDecl := { tmpDecl with name := declName }
  decls.binSearch tmpDecl declLt

@[expose] def DeclExt (pu : Purity) :=
   PersistentEnvExtension (Decl pu) (Decl pu) (DeclExtState pu)

instance : Inhabited (DeclExt pu) :=
  inferInstanceAs (Inhabited (PersistentEnvExtension (Decl pu) (Decl pu) (DeclExtState pu)))

def mkDeclExt (phase : Phase) (name : Name := by exact decl_name%) :
    IO (DeclExt phase.toPurity) :=
  registerPersistentEnvExtension {
    name,
    mkInitial := pure {},
    addImportedFn := fun _ => pure {},
    addEntryFn := fun s decl => s.insert decl.name decl
    exportEntriesFnEx env s level := Id.run do
      let mut entries := sortedDecls s
      if level != .private then
        entries := entries.filterMap fun decl => do
          guard <| isDeclPublic env decl.name
          if isDeclTransparent env phase decl.name then
            some decl
          else
            some { decl with value := .extern { entries := [.opaque] } }
      return entries
    statsFn := fun s =>
      let numEntries := s.foldl (init := 0) (fun count _ _ => count + 1)
      format "number of local entries: " ++ format numEntries
    asyncMode := .sync,
    replay? := some <| fun oldState newState _ otherState =>
      newState.foldl (init := otherState) fun otherState k v =>
        if oldState.contains k then
          otherState
        else
          otherState.insert k v
  }

builtin_initialize baseExt : DeclExt .pure ← mkDeclExt .base
builtin_initialize monoExt : DeclExt .pure ← mkDeclExt .mono
builtin_initialize impureExt : DeclExt .impure ← mkDeclExt .impure

def getDeclCore? (env : Environment) (ext : DeclExt pu) (declName : Name) : Option (Decl pu) :=
  match env.getModuleIdxFor? declName with
  | some modIdx => findAtSorted? (ext.getModuleEntries env modIdx) declName
  | none        => ext.getState env |>.find? declName

def getBaseDecl? (declName : Name) : CoreM (Option (Decl .pure)) := do
  return getDeclCore? (← getEnv) baseExt declName

def getMonoDecl? (declName : Name) : CoreM (Option (Decl .pure)) := do
  return getDeclCore? (← getEnv) monoExt declName

def getImpureDecl? (declName : Name) : CoreM (Option (Decl .impure)) := do
  return getDeclCore? (← getEnv) impureExt declName

def saveBaseDeclCore (env : Environment) (decl : Decl .pure) : Environment :=
  baseExt.addEntry env decl

def saveMonoDeclCore (env : Environment) (decl : Decl .pure) : Environment :=
  monoExt.addEntry env decl

def saveImpureDeclCore (env : Environment) (decl : Decl .impure) : Environment :=
  impureExt.addEntry env decl

def Decl.saveBase (decl : Decl .pure) : CoreM Unit :=
  modifyEnv (saveBaseDeclCore · decl)

def Decl.saveMono (decl : Decl .pure) : CoreM Unit :=
  modifyEnv (saveMonoDeclCore · decl)

def Decl.saveImpure (decl : Decl .impure) : CoreM Unit :=
  modifyEnv (saveImpureDeclCore · decl)

def Decl.save (decl : Decl pu) : CompilerM Unit := do
  match (← getPhase) with
  | .base => Phase.withPurityCheck .base pu fun h =>
      (h.symm ▸ decl).saveBase
  | .mono => Phase.withPurityCheck .mono pu fun h =>
      (h.symm ▸ decl).saveMono
  | .impure => Phase.withPurityCheck .impure pu fun h =>
      (h.symm ▸ decl).saveImpure

def getDeclAt? (declName : Name) (phase : Phase) : CoreM (Option (Decl phase.toPurity)) :=
  match phase with
  | .base => getBaseDecl? declName
  | .mono => getMonoDecl? declName
  | .impure => getImpureDecl? declName

@[inline]
def getDecl? (declName : Name) : CompilerM (Option ((pu : Purity) × Decl pu)) := do
  let some decl ← getDeclAt? declName (← getPhase) | return none
  return some ⟨_, decl⟩

def getLocalDeclAt? (declName : Name) (phase : Phase) : CompilerM (Option (Decl phase.toPurity)) := do
  match phase with
  | .base => return baseExt.getState (← getEnv) |>.find? declName
  | .mono => return monoExt.getState (← getEnv) |>.find? declName
  | .impure => return impureExt.getState (← getEnv) |>.find? declName

@[inline]
def getLocalDecl? (declName : Name) : CompilerM (Option ((pu : Purity) × Decl pu)) := do
  let some decl ← getLocalDeclAt? declName (← getPhase) | return none
  return some ⟨_, decl⟩

def getExt (phase : Phase) : DeclExt phase.toPurity :=
  match phase with
  | .base => baseExt
  | .mono => monoExt
  | .impure => impureExt

end Lean.Compiler.LCNF
