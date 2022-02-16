/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.DeclarationRange
import Lean.MonadEnv

namespace Lean

private builtin_initialize builtinDocStrings : IO.Ref (NameMap String) ← IO.mkRef {}
private builtin_initialize docStringExt : MapDeclarationExtension String ← mkMapDeclarationExtension `docstring

def addBuiltinDocString (declName : Name) (docString : String) : IO Unit :=
  builtinDocStrings.modify (·.insert declName docString)

def addDocString [MonadEnv m] (declName : Name) (docString : String) : m Unit :=
  modifyEnv fun env => docStringExt.insert env declName docString

def addDocString' [Monad m] [MonadEnv m] (declName : Name) (docString? : Option String) : m Unit :=
  match docString? with
  | some docString => addDocString declName docString
  | none => return ()

def findDocString? (env : Environment) (declName : Name) : IO (Option String) :=
  return (← builtinDocStrings.get).find? declName |>.orElse fun _ => docStringExt.find? env declName

structure ModuleDoc where
  doc : String
  declarationRange : DeclarationRange

private builtin_initialize moduleDocExt : SimplePersistentEnvExtension ModuleDoc (Std.PersistentArray ModuleDoc) ← registerSimplePersistentEnvExtension {
  name          := `moduleDocExt
  addImportedFn := fun _ => {}
  addEntryFn    := fun s e => s.push e
  toArrayFn     := fun es => es.toArray
}

def addMainModuleDoc (env : Environment) (doc : ModuleDoc) : Environment :=
  moduleDocExt.addEntry env doc

def getMainModuleDoc (env : Environment) : Std.PersistentArray ModuleDoc :=
  moduleDocExt.getState env

def getModuleDoc? (env : Environment) (moduleName : Name) : Option (Array ModuleDoc) :=
  env.getModuleIdx? moduleName |>.map fun modIdx => moduleDocExt.getModuleEntries env modIdx

end Lean
