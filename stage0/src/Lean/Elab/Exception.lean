/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.InternalExceptionId
import Lean.Meta.Basic

namespace Lean.Elab

builtin_initialize postponeExceptionId : InternalExceptionId ← registerInternalExceptionId `postpone
builtin_initialize unsupportedSyntaxExceptionId : InternalExceptionId ← registerInternalExceptionId `unsupportedSyntax
builtin_initialize abortExceptionId : InternalExceptionId ← registerInternalExceptionId `abortElab
builtin_initialize autoBoundImplicitExceptionId : InternalExceptionId ← registerInternalExceptionId `autoBoundImplicit

def throwPostpone [MonadExceptOf Exception m] : m α :=
  throw $ Exception.internal postponeExceptionId

def throwUnsupportedSyntax [MonadExceptOf Exception m] : m α :=
  throw $ Exception.internal unsupportedSyntaxExceptionId

def throwIllFormedSyntax [Monad m] [MonadError m] : m α :=
  throwError "ill-formed syntax"

def throwAutoBoundImplicitLocal [MonadExceptOf Exception m] (n : Name) : m α :=
  throw $ Exception.internal autoBoundImplicitExceptionId <| KVMap.empty.insert `localId n

def isAutoBoundImplicitLocalException? (ex : Exception) : Option Name :=
  match ex with
  | Exception.internal id k =>
    if id == autoBoundImplicitExceptionId then
      some <| k.getName `localId `x
    else
      none
  | _ => none

def throwAlreadyDeclaredUniverseLevel [Monad m] [MonadError m] (u : Name) : m α :=
  throwError! "a universe level named '{u}' has already been declared"

-- Throw exception to abort elaboration without producing any error message
def throwAbort {α m} [MonadExcept Exception m] : m α :=
  throw $ Exception.internal abortExceptionId

def mkMessageCore (fileName : String) (fileMap : FileMap) (msgData : MessageData) (severity : MessageSeverity) (pos : String.Pos) : Message :=
  let pos := fileMap.toPosition pos
  { fileName := fileName, pos := pos, data := msgData, severity := severity }

end Lean.Elab
