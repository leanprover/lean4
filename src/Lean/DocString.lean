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

private def findLeadingSpacesSize (s : String) : Nat :=
  let it := s.iter
  let it := it.find (· == '\n') |>.next
  let (min, it) := it.foldUntil 0 fun num c => if c == ' ' || c == '\t' then some (num + 1) else none
  findNextLine it min
where
  consumeSpaces (it : String.Iterator) (curr min : Nat) : Nat :=
    if it.atEnd then min
    else if it.curr == ' ' || it.curr == '\t' then consumeSpaces it.next (curr + 1) min
    else findNextLine it.next (Nat.min curr min)
  findNextLine (it : String.Iterator) (min : Nat) : Nat :=
    if it.atEnd then min
    else if it.curr == '\n' then consumeSpaces it.next 0 min
    else findNextLine it.next min

private def removeNumLeadingSpaces (n : Nat) (s : String) : String :=
  consumeSpaces n s.iter ""
where
  consumeSpaces (n : Nat) (it : String.Iterator) (r : String) : String :=
     match n with
     | 0 => saveLine it r
     | n+1 =>
       if it.atEnd then r
       else if it.curr == ' ' || it.curr == '\t' then consumeSpaces n it.next r
       else saveLine it r
  saveLine (it : String.Iterator) (r : String) : String :=
    if it.atEnd then r
    else if it.curr == '\n' then consumeSpaces n it.next (r.push '\n')
    else saveLine it.next (r.push it.curr)
termination_by
  consumeSpaces n it r => (it, 1)
  saveLine it r => (it, 0)

private def removeLeadingSpaces (s : String) : String :=
  let n := findLeadingSpacesSize s
  if n == 0 then s else removeNumLeadingSpaces n s

def addBuiltinDocString (declName : Name) (docString : String) : IO Unit :=
  builtinDocStrings.modify (·.insert declName (removeLeadingSpaces docString))

def addDocString [MonadEnv m] (declName : Name) (docString : String) : m Unit :=
  modifyEnv fun env => docStringExt.insert env declName (removeLeadingSpaces docString)

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

def getDocStringText [Monad m] [MonadError m] [MonadRef m] (stx : TSyntax `Lean.Parser.Command.docComment) : m String :=
  match stx.raw[1] with
  | Syntax.atom _ val => return val.extract 0 (val.endPos - ⟨2⟩)
  | _                 => throwErrorAt stx "unexpected doc string{indentD stx.raw[1]}"

end Lean
