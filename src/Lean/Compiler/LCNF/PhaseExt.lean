/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.LCNF.PassManager
public import Lean.Compiler.LCNF.PublicDeclsExt

public section

namespace Lean.Compiler.LCNF

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

abbrev AbstractDeclExtState (pu : Purity) (β : Purity → Type) := PHashMap Name (β pu)

private def sortedEntries (s : AbstractDeclExtState pu β) (lt : β pu → β pu → Bool) : Array (β pu) :=
  let decls := s.foldl (init := #[]) fun ps _ v => ps.push v
  decls.qsort lt

private def replayFn (phase : Phase) : ReplayFn (AbstractDeclExtState phase.toPurity β) :=
  fun oldState newState _ otherState =>
    newState.foldl (init := otherState) fun otherState k v =>
      if oldState.contains k then
        otherState
      else
        otherState.insert k v

private def statsFn (state : AbstractDeclExtState pu β) : Format :=
  let numEntries := state.foldl (init := 0) (fun count _ _ => count + 1)
  format "number of local entries: " ++ format numEntries

abbrev DeclExtState (pu : Purity) := AbstractDeclExtState pu Decl

private abbrev declLt (a b : Decl pu) :=
  Name.quickLt a.name b.name

private abbrev findDeclAtSorted? (decls : Array (Decl pu)) (declName : Name) : Option (Decl pu) :=
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
      let mut entries := sortedEntries s declLt
      if level != .private then
        entries := entries.filterMap fun decl => do
          guard <| isDeclPublic env decl.name
          if isDeclTransparent env phase decl.name then
            some decl
          else
            some { decl with value := .extern { entries := [.opaque] } }
      return entries
    statsFn := statsFn,
    asyncMode := .sync,
    replay? := some (replayFn phase)
  }


builtin_initialize baseExt : DeclExt .pure ← mkDeclExt .base
builtin_initialize monoExt : DeclExt .pure ← mkDeclExt .mono
builtin_initialize impureExt : EnvExtension (DeclExtState .impure) ←
  registerEnvExtension (mkInitial := pure {}) (asyncMode := .sync) (replay? := some (replayFn .impure))


abbrev SigExtState (pu : Purity) := AbstractDeclExtState pu Signature

@[expose] def SigExt (pu : Purity) :=
   PersistentEnvExtension (Signature pu) (Signature pu) (SigExtState pu)

instance : Inhabited (SigExt pu) :=
  inferInstanceAs (Inhabited (PersistentEnvExtension (Signature pu) (Signature pu) (SigExtState pu)))

private abbrev sigLt (a b : Signature pu) :=
  Name.quickLt a.name b.name

private abbrev findSigAtSorted? (sigs : Array (Signature pu)) (declName : Name) : Option (Signature pu) :=
  let tmpSig : Signature pu := default
  let tmpSig := { tmpSig with name := declName }
  sigs.binSearch tmpSig sigLt

def mkSigDeclExt (phase : Phase) (name : Name := by exact decl_name%) :
    IO (SigExt phase.toPurity) :=
  registerPersistentEnvExtension {
    name,
    mkInitial := pure {},
    addImportedFn := fun _ => pure {},
    addEntryFn := fun s sig => s.insert sig.name sig
    exportEntriesFnEx env s level := Id.run do
      let mut entries := sortedEntries s sigLt
      if level != .private then
        entries := entries.filterMap fun sig => do
          guard <| isDeclPublic env sig.name
          some sig
      return entries
    statsFn := statsFn,
    asyncMode := .sync,
    replay? := some (replayFn phase)
  }

builtin_initialize impureSigExt : SigExt .impure ← mkSigDeclExt .impure

def getDeclCore? (env : Environment) (ext : DeclExt pu) (declName : Name) : Option (Decl pu) :=
  match env.getModuleIdxFor? declName with
  | some modIdx => findDeclAtSorted? (ext.getModuleEntries env modIdx) declName
  | none        => ext.getState env |>.find? declName

def getSigCore? (env : Environment) (ext : SigExt pu) (declName : Name) : Option (Signature pu) :=
  match env.getModuleIdxFor? declName with
  | some modIdx => findSigAtSorted? (ext.getModuleEntries env modIdx) declName
  | none        => ext.getState env |>.find? declName

def getBaseDecl? (declName : Name) : CoreM (Option (Decl .pure)) := do
  return getDeclCore? (← getEnv) baseExt declName

def getMonoDecl? (declName : Name) : CoreM (Option (Decl .pure)) := do
  return getDeclCore? (← getEnv) monoExt declName

def getLocalImpureDecl? (declName : Name) : CoreM (Option (Decl .impure)) := do
  return impureExt.getState (← getEnv) |>.find? declName

def getImpureSignature? (declName : Name) : CoreM (Option (Signature .impure)) := do
  return getSigCore? (← getEnv) impureSigExt declName

def saveBaseDeclCore (env : Environment) (decl : Decl .pure) : Environment :=
  baseExt.addEntry env decl

def saveMonoDeclCore (env : Environment) (decl : Decl .pure) : Environment :=
  monoExt.addEntry env decl

def saveImpureDeclCore (env : Environment) (decl : Decl .impure) : Environment :=
  let env := impureExt.modifyState env (fun s => s.insert decl.name decl)
  impureSigExt.addEntry env decl.toSignature

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
  | .impure => throwError "Internal compiler error: getDecl? on impure is unuspported for now"

@[inline]
def getDecl? (declName : Name) : CompilerM (Option ((pu : Purity) × Decl pu)) := do
  let some decl ← getDeclAt? declName (← getPhase) | return none
  return some ⟨_, decl⟩

def getLocalDeclAt? (declName : Name) (phase : Phase) : CompilerM (Option (Decl phase.toPurity)) :=
  match phase with
  | .base => return baseExt.getState (← getEnv) |>.find? declName
  | .mono => return monoExt.getState (← getEnv) |>.find? declName
  | .impure => return impureExt.getState (← getEnv) |>.find? declName

@[inline]
def getLocalDecl? (declName : Name) : CompilerM (Option ((pu : Purity) × Decl pu)) := do
  let some decl ← getLocalDeclAt? declName (← getPhase) | return none
  return some ⟨_, decl⟩

end Lean.Compiler.LCNF
