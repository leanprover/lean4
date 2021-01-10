/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.MonadEnv

namespace Lean

builtin_initialize docStringExt : SimplePersistentEnvExtension (Name × String) (NameMap String) ←
  registerSimplePersistentEnvExtension {
    name          := `docstring,
    addImportedFn := fun as => {},
    addEntryFn    := fun s p => s.insert p.1 p.2,
    toArrayFn     := fun es => es.toArray.qsort (fun a b => Name.quickLt a.1 b.1)
  }

def addDocString [MonadEnv m] (declName : Name) (docString : String) : m Unit :=
  modifyEnv fun env => docStringExt.addEntry env (declName, docString)

def getDocString? [Monad m] [MonadEnv m] (declName : Name) : m (Option String) := do
  let env ← getEnv
  match env.getModuleIdxFor? declName with
  | some modIdx =>
    match (docStringExt.getModuleEntries env modIdx).binSearch (declName, arbitrary) (fun a b => Name.quickLt a.1 b.1) with
    | some e => return some e.2
    | none   => return none
  | none => return (docStringExt.getState env).find? declName

end Lean
