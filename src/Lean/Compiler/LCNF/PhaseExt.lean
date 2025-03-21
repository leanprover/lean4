/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Compiler.LCNF.PassManager

namespace Lean.Compiler.LCNF

abbrev DeclExtState := PHashMap Name Decl

private abbrev declLt (a b : Decl) :=
  Name.quickLt a.name b.name

private abbrev sortDecls (decls : Array Decl) : Array Decl :=
  decls.qsort declLt

private abbrev findAtSorted? (decls : Array Decl) (declName : Name) : Option Decl :=
  let tmpDecl : Decl := default
  let tmpDecl := { tmpDecl with name := declName }
  decls.binSearch tmpDecl declLt

abbrev DeclExt := PersistentEnvExtension Decl Decl DeclExtState

def mkDeclExt (name : Name := by exact decl_name%) : IO DeclExt := do
  registerPersistentEnvExtension {
    name            := name
    mkInitial       := return {}
    addImportedFn   := fun _ => return {}
    addEntryFn      := fun decls decl => decls.insert decl.name decl
    exportEntriesFn := fun s =>
      let decls := s.foldl (init := #[]) fun decls _ decl => decls.push decl
      sortDecls decls
    asyncMode       := .sync  -- compilation is non-parallel anyway
  }

builtin_initialize baseExt : PersistentEnvExtension Decl Decl DeclExtState ← mkDeclExt
builtin_initialize monoExt : PersistentEnvExtension Decl Decl DeclExtState ← mkDeclExt

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
  | _ => unreachable!

def getDeclAt? (declName : Name) (phase : Phase) : CoreM (Option Decl) :=
  match phase with
  | .base => getBaseDecl? declName
  | .mono => getMonoDecl? declName
  | _  => return none -- TODO

def getDecl? (declName : Name) : CompilerM (Option Decl) := do
  getDeclAt? declName (← getPhase)

def getExt (phase : Phase) : DeclExt :=
  match phase with
  | .base => baseExt
  | .mono => monoExt
  | _ => unreachable!

def forEachDecl (f : Decl → CoreM Unit) (phase := Phase.base) : CoreM Unit := do
  let ext := getExt phase
  let env ← getEnv
  for modIdx in [:env.allImportedModuleNames.size] do
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
