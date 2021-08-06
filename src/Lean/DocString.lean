/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.MonadEnv

namespace Lean

private builtin_initialize docStringExt : MapDeclarationExtension String ← mkMapDeclarationExtension `docstring

def addDocString [MonadEnv m] (declName : Name) (docString : String) : m Unit :=
  modifyEnv fun env => docStringExt.insert env declName docString

def addDocString' [Monad m] [MonadEnv m] (declName : Name) (docString? : Option String) : m Unit :=
  match docString? with
  | some docString => addDocString declName docString
  | none => return ()

def findDocString? [Monad m] [MonadEnv m] (declName : Name) : m (Option String) :=
  return docStringExt.find? (← getEnv) declName

private builtin_initialize moduleDocExt : SimplePersistentEnvExtension String (Std.PersistentArray String) ← registerSimplePersistentEnvExtension {
  name          := `moduleDocExt
  addImportedFn := fun _ => {}
  addEntryFn    := fun s e => s.push e
  toArrayFn     := fun es => es.toArray
}

def addMainModuleDoc (env : Environment) (doc : String) : Environment :=
  moduleDocExt.addEntry env doc

def getMainModuleDoc (env : Environment)  : Std.PersistentArray String :=
  moduleDocExt.getState env

def getModuleDoc? (env : Environment) (moduleName : Name) : Option (Array String) :=
  env.getModuleIdx? moduleName |>.map fun modIdx => moduleDocExt.getModuleEntries env modIdx

end Lean
