/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.MonadEnv

namespace Lean

builtin_initialize docStringExt : MapDeclarationExtension String ← mkMapDeclarationExtension `docstring

def addDocString [MonadEnv m] (declName : Name) (docString : String) : m Unit :=
  modifyEnv fun env => docStringExt.insert env declName docString

def addDocString' [Monad m] [MonadEnv m] (declName : Name) (docString? : Option String) : m Unit :=
  match docString? with
  | some docString => addDocString declName docString
  | none => return ()

def getDocString? [Monad m] [MonadEnv m] (declName : Name) : m (Option String) :=
  return docStringExt.find? (← getEnv) declName

end Lean
