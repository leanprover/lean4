/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.PassManager

namespace Lean.Compiler.LCNF

abbrev BaseExtState := PHashMap Name Decl

private abbrev declLt (a b : Decl) :=
  Name.quickLt a.name b.name

private abbrev sortDecls (decls : Array Decl) : Array Decl :=
  decls.qsort declLt

private abbrev findAtSorted? (decls : Array Decl) (declName : Name) : Option Decl :=
  let tmpDecl : Decl := default
  let tmpDecl := { tmpDecl with name := declName }
  decls.binSearch tmpDecl declLt

builtin_initialize baseExt : PersistentEnvExtension Decl Decl BaseExtState ← do
  registerPersistentEnvExtension {
    name            := `compBaseDecls
    mkInitial       := return {}
    addImportedFn   := fun _ => return {}
    addEntryFn      := fun decls decl => decls.insert decl.name decl
    exportEntriesFn := fun s =>
      let decls := s.foldl (init := #[]) fun decls _ decl => decls.push decl
      sortDecls decls
  }

def getBaseDeclCore? (env : Environment) (declName : Name) : Option Decl :=
  match env.getModuleIdxFor? declName with
  | some modIdx => findAtSorted? (baseExt.getModuleEntries env modIdx) declName
  | none        => baseExt.getState env |>.find? declName

def getBaseDecl? (declName : Name) : CoreM (Option Decl) := do
  return getBaseDeclCore? (← getEnv) declName

def saveBaseDeclCore (env : Environment) (decl : Decl) : Environment :=
  let env := env.addExtraName decl.name
  baseExt.addEntry env decl

def Decl.saveBase (decl : Decl) : CoreM Unit :=
  modifyEnv (saveBaseDeclCore · decl)

def getDeclAt? (declName : Name) (phase : Phase) : CoreM (Option Decl) :=
  match phase with
  | .base => getBaseDecl? declName
  | _  => return none -- TODO

def getDecl? (declName : Name) : CompilerM (Option Decl) := do
  getDeclAt? declName (← getPhase)

def normalizeFVarIds (decl : Decl) : CoreM Decl := do
  let ngenSaved ← getNGen
  setNGen {}
  try
    CompilerM.run <| decl.internalize
  finally
    setNGen ngenSaved

def saveBase : Pass :=
  .mkPerDeclaration `saveBase (fun decl => do (← normalizeFVarIds decl).saveBase; return decl) .base

def forEachDecl (f : Decl → CoreM Unit) : CoreM Unit := do
  let env ← getEnv
  for modIdx in [:env.allImportedModuleNames.size] do
    for decl in baseExt.getModuleEntries env modIdx do
      f decl
  baseExt.getState env |>.forM fun _ decl => f decl

def forEachModuleDecl (moduleName : Name) (f : Decl → CoreM Unit) : CoreM Unit := do
  let env ← getEnv
  let some modIdx := env.getModuleIdx? moduleName | throwError "module `{moduleName}` not found"
  for decl in baseExt.getModuleEntries env modIdx do
    f decl

def forEachMainModuleDecl (f : Decl → CoreM Unit) : CoreM Unit := do
  baseExt.getState (← getEnv) |>.forM fun _ decl => f decl

end Lean.Compiler.LCNF
