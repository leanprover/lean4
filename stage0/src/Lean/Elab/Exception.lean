#lang lean4
/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.InternalExceptionId
import Lean.Meta.Basic

namespace Lean.Elab
initialize postponeExceptionId : InternalExceptionId ← registerInternalExceptionId `postpone
initialize unsupportedSyntaxExceptionId : InternalExceptionId ← registerInternalExceptionId `unsupportedSyntax
initialize abortExceptionId : InternalExceptionId ← registerInternalExceptionId `abortElab

def throwPostpone {α m} [MonadExceptOf Exception m] : m α :=
throw $ Exception.internal postponeExceptionId

def throwUnsupportedSyntax {α m} [MonadExceptOf Exception m] : m α :=
throw $ Exception.internal unsupportedSyntaxExceptionId

def throwIllFormedSyntax {α m} [Monad m] [MonadExceptOf Exception m] [Ref m] [AddErrorMessageContext m] : m α :=
throwError "ill-formed syntax"

def throwAlreadyDeclaredUniverseLevel {α m} [Monad m] [MonadExceptOf Exception m] [Ref m] [AddErrorMessageContext m] (u : Name) : m α :=
throwError! "a universe level named '{u}' has already been declared"

-- Throw exception to abort elaboration without producing any error message
def throwAbort {α m} [MonadExcept Exception m] : m α :=
throw $ Exception.internal abortExceptionId

def mkMessageCore (fileName : String) (fileMap : FileMap) (msgData : MessageData) (severity : MessageSeverity) (pos : String.Pos) : Message :=
let pos := fileMap.toPosition pos
{ fileName := fileName, pos := pos, data := msgData, severity := severity }

end Lean.Elab
