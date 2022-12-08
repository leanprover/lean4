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
builtin_initialize abortCommandExceptionId : InternalExceptionId ← registerInternalExceptionId `abortCommandElab
builtin_initialize abortTermExceptionId : InternalExceptionId ← registerInternalExceptionId `abortTermElab
builtin_initialize abortTacticExceptionId : InternalExceptionId ← registerInternalExceptionId `abortTactic
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
  throwError "a universe level named '{u}' has already been declared"

-- Throw exception to abort elaboration of the current command without producing any error message
def throwAbortCommand {α m} [MonadExcept Exception m] : m α :=
  throw <| Exception.internal abortCommandExceptionId

-- Throw exception to abort elaboration of the current term without producing any error message
def throwAbortTerm {α m} [MonadExcept Exception m] : m α :=
  throw <| Exception.internal abortTermExceptionId

-- Throw exception to abort evaluation of the current tactic without producing any error message
def throwAbortTactic {α m} [MonadExcept Exception m] : m α :=
  throw <| Exception.internal abortTacticExceptionId

def isAbortTacticException (ex : Exception) : Bool :=
  match ex with
  | Exception.internal id .. => id == abortTacticExceptionId
  | _ => false

def isAbortExceptionId (id : InternalExceptionId) : Bool :=
  id == abortCommandExceptionId || id == abortTermExceptionId || id == abortTacticExceptionId

def mkMessageCore (fileName : String) (fileMap : FileMap) (data : MessageData) (severity : MessageSeverity) (pos : String.Pos) (endPos : String.Pos) : Message :=
  let pos := fileMap.toPosition pos
  let endPos := fileMap.toPosition endPos
  { fileName, pos, endPos, data, severity }

end Lean.Elab
