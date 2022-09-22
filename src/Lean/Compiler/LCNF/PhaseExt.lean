/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.PassManager

namespace Lean.Compiler.LCNF

abbrev BaseExtState := Std.PHashMap Name Decl

private abbrev declLt (a b : Decl) :=
  Name.quickLt a.name b.name

private abbrev sortDecls (decls : Array Decl) : Array Decl :=
  decls.qsort declLt

private abbrev findAtSorted? (decls : Array Decl) (declName : Name) : Option Decl :=
  let tmpDecl : Decl := default
  let tmpDecl := { tmpDecl with name := declName }
  decls.binSearch tmpDecl declLt

builtin_initialize baseExt : SimplePersistentEnvExtension Decl BaseExtState ← do
  registerSimplePersistentEnvExtension {
    name          := `baseDecls
    addImportedFn := fun _ => {}
    addEntryFn    := fun decls decl => decls.insert decl.name decl
    toArrayFn     := fun es => sortDecls es.toArray
  }

def getBaseDeclCore? (env : Environment) (declName : Name) : Option Decl :=
  match env.getModuleIdxFor? declName with
  | some modIdx => findAtSorted? (baseExt.getModuleEntries env modIdx) declName
  | none        => dbg_trace "getBaseDeclCore?"; baseExt.getState env |>.find? declName

def getBaseDecl? (declName : Name) : CoreM (Option Decl) := do
  IO.println s!">> getBaseDecl? {declName}"
  return getBaseDeclCore? (← getEnv) declName

def saveBaseDeclCore (env : Environment) (decl : Decl) : Environment :=
  baseExt.addEntry env decl

def Decl.saveBase (decl : Decl) : CoreM Unit := do
  IO.println "saving"
  IO.println decl.name
  modifyEnv (saveBaseDeclCore · decl)

def getDecl? (phase : Phase) (declName : Name) : CoreM (Option Decl) :=
  match phase with
  | .base => getBaseDecl? declName
  | _  => return none -- TODO

def saveBase : Pass :=
  .mkPerDeclaration `saveBase (fun decl => do decl.saveBase; return decl) .base

end Lean.Compiler.LCNF