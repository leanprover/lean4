/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Compiler.LCNF.PassManager

namespace Lean.Compiler.LCNF

/-- Modifiers adjusting export behavior of compiler declarations for `import`. -/
inductive DeclVisibility where
  /-- Do not export. -/
  | «private»
  /-- Export signature only, as `opaque` extern. -/
  | «opaque»
  /-- Export full LCNF, IR signatures. -/
  | transparent
deriving Inhabited, BEq, Repr, Ord

instance : LE DeclVisibility := leOfOrd

/-- Visibility of local declarations, not persisted. -/
private builtin_initialize declVisibilityExt : EnvExtension (List Name × NameMap DeclVisibility) ←
  registerEnvExtension
    (mkInitial := pure ([], {}))
    (asyncMode := .sync)
    (replay? := some <| fun oldState newState _ s =>
      let newEntries := newState.1.take (newState.1.length - oldState.1.length)
      newEntries.foldl (init := s) fun s n =>
        if s.1.contains n then
          s
        else
          (n :: s.1, s.2.insert n (newState.2.find? n).get!))

def getDeclVisibility (env : Environment) (declName : Name) : DeclVisibility :=
  -- The IR compiler may call the boxed variant it introduces after we do visibility inference, so
  -- use same visibility as base decl.
  let inferFor := match declName with
    | .str n "_boxed" => n
    | n               => n
  declVisibilityExt.getState env |>.2.find? inferFor
    |>.getD (if env.header.isModule then .private else .transparent)

def bumpDeclVisibility (env : Environment) (declName : Name) (visibility : DeclVisibility) : Environment :=
  if getDeclVisibility env declName ≥ visibility then
    env
  else
    declVisibilityExt.modifyState env fun s =>
      (declName :: s.1, s.2.insert declName visibility)

abbrev DeclExtState := PHashMap Name Decl

private abbrev declLt (a b : Decl) :=
  Name.quickLt a.name b.name

private def sortedDecls (s : DeclExtState) : Array Decl :=
  let decls := s.foldl (init := #[]) fun ps _ v => ps.push v
  decls.qsort declLt

private abbrev findAtSorted? (decls : Array Decl) (declName : Name) : Option Decl :=
  let tmpDecl : Decl := default
  let tmpDecl := { tmpDecl with name := declName }
  decls.binSearch tmpDecl declLt

def DeclExt := PersistentEnvExtension Decl Decl DeclExtState

instance : Inhabited DeclExt :=
  inferInstanceAs (Inhabited (PersistentEnvExtension Decl Decl DeclExtState))

def mkDeclExt (name : Name := by exact decl_name%) : IO DeclExt :=
  registerPersistentEnvExtension {
    name,
    mkInitial := pure {},
    addImportedFn := fun _ => pure {},
    addEntryFn := fun s decl => s.insert decl.name decl
    exportEntriesFnEx env s level := Id.run do
      let mut entries := sortedDecls s
      if level != .private then
        entries := entries.filterMap fun decl =>
          match getDeclVisibility env decl.name with
          | .private => none
          | .opaque => some { decl with
            value := .extern { arity? := decl.getArity, entries := [.opaque decl.name] } }
          | _ => some decl
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

builtin_initialize baseExt : DeclExt ← mkDeclExt
builtin_initialize monoExt : DeclExt ← mkDeclExt

def getDeclCore? (env : Environment) (ext : DeclExt) (declName : Name) : Option Decl :=
  match env.getModuleIdxFor? declName with
  | some modIdx => findAtSorted? (ext.getModuleEntries env modIdx) declName
  | none        => ext.getState env |>.find? declName

def getBaseDecl? (declName : Name) : CoreM (Option Decl) := do
  return getDeclCore? (← getEnv) baseExt declName

def getMonoDecl? (declName : Name) : CoreM (Option Decl) := do
  return getDeclCore? (← getEnv) monoExt declName

def saveBaseDeclCore (env : Environment) (decl : Decl) : Environment :=
  baseExt.addEntry (env.addExtraName decl.name) decl

def saveMonoDeclCore (env : Environment) (decl : Decl) : Environment :=
  monoExt.addEntry (env.addExtraName decl.name) decl

def Decl.saveBase (decl : Decl) : CoreM Unit :=
  modifyEnv (saveBaseDeclCore · decl)

def Decl.saveMono (decl : Decl) : CoreM Unit :=
  modifyEnv (saveMonoDeclCore · decl)

def Decl.save (decl : Decl) : CompilerM Unit := do
  match (← getPhase) with
  | .base => decl.saveBase
  | .mono => decl.saveMono

def getDeclAt? (declName : Name) (phase : Phase) : CoreM (Option Decl) :=
  match phase with
  | .base => getBaseDecl? declName
  | .mono => getMonoDecl? declName

def getDecl? (declName : Name) : CompilerM (Option Decl) := do
  getDeclAt? declName (← getPhase)

def getExt (phase : Phase) : DeclExt :=
  match phase with
  | .base => baseExt
  | .mono => monoExt

def forEachDecl (f : Decl → CoreM Unit) (phase := Phase.base) : CoreM Unit := do
  let ext := getExt phase
  let env ← getEnv
  for modIdx in *...env.allImportedModuleNames.size do
    for decl in ext.getModuleEntries env modIdx do
      f decl
  ext.getState env |>.forM fun _ decl => f decl

def forEachModuleDecl (moduleName : Name) (f : Decl → CoreM Unit) (phase := Phase.base) : CoreM Unit := do
  let ext := getExt phase
  let env ← getEnv
  let some modIdx := env.getModuleIdx? moduleName | throwError "module `{moduleName}` not found"
  for decl in ext.getModuleEntries env modIdx do
    f decl

def forEachMainModuleDecl (f : Decl → CoreM Unit) (phase := Phase.base) : CoreM Unit := do
  (getExt phase).getState (← getEnv) |>.forM fun _ decl => f decl

end Lean.Compiler.LCNF
