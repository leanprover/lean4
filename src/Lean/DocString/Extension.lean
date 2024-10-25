/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.DeclarationRange
import Lean.MonadEnv
import Init.Data.String.Extra

-- This module contains the underlying data for docstrings, with as few imports as possible, so that
-- docstrings can be saved in as much of the compiler as possible.
-- The module `Lean.DocString` contains the query interface, which needs to look at additional data
-- to construct user-visible docstrings.

namespace Lean

private builtin_initialize builtinDocStrings : IO.Ref (NameMap String) ← IO.mkRef {}
builtin_initialize docStringExt : MapDeclarationExtension String ← mkMapDeclarationExtension

def addBuiltinDocString (declName : Name) (docString : String) : IO Unit :=
  builtinDocStrings.modify (·.insert declName docString.removeLeadingSpaces)

def addDocString [Monad m] [MonadError m] [MonadEnv m] (declName : Name) (docString : String) : m Unit := do
  unless (← getEnv).getModuleIdxFor? declName |>.isNone do
    throwError s!"invalid doc string, declaration '{declName}' is in an imported module"
  modifyEnv fun env => docStringExt.insert env declName docString.removeLeadingSpaces

def addDocString' [Monad m] [MonadError m] [MonadEnv m] (declName : Name) (docString? : Option String) : m Unit :=
  match docString? with
  | some docString => addDocString declName docString
  | none => return ()

/--
Finds a docstring without performing any alias resolution or enrichment with extra metadata.

Docstrings to be shown to a user should be looked up with `Lean.findDocString?` instead.
-/
def findSimpleDocString? (env : Environment) (declName : Name) (includeBuiltin := true) : IO (Option String) :=
  if let some docStr := docStringExt.find? env declName then
    return some docStr
  else if includeBuiltin then
    return (← builtinDocStrings.get).find? declName
  else
    return none

structure ModuleDoc where
  doc : String
  declarationRange : DeclarationRange

private builtin_initialize moduleDocExt : SimplePersistentEnvExtension ModuleDoc (PersistentArray ModuleDoc) ← registerSimplePersistentEnvExtension {
  addImportedFn := fun _ => {}
  addEntryFn    := fun s e => s.push e
  toArrayFn     := fun es => es.toArray
}

def addMainModuleDoc (env : Environment) (doc : ModuleDoc) : Environment :=
  moduleDocExt.addEntry env doc

def getMainModuleDoc (env : Environment) : PersistentArray ModuleDoc :=
  moduleDocExt.getState env

def getModuleDoc? (env : Environment) (moduleName : Name) : Option (Array ModuleDoc) :=
  env.getModuleIdx? moduleName |>.map fun modIdx => moduleDocExt.getModuleEntries env modIdx

def getDocStringText [Monad m] [MonadError m] (stx : TSyntax `Lean.Parser.Command.docComment) : m String :=
  match stx.raw[1] with
  | Syntax.atom _ val => return val.extract 0 (val.endPos - ⟨2⟩)
  | _                 => throwErrorAt stx "unexpected doc string{indentD stx.raw[1]}"
