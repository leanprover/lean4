/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Init.System.IOError
import Lean.InternalExceptionId
import Lean.Meta.Exception

namespace Lean
namespace Elab

def registerPostponeId : IO InternalExceptionId :=
registerInternalExceptionId `postpone
@[init registerPostponeId]
constant postponeExceptionId : InternalExceptionId := arbitrary _

def registerUnsupportedSyntaxId : IO InternalExceptionId :=
registerInternalExceptionId `unsupportedSyntax
@[init registerUnsupportedSyntaxId]
constant unsupportedSyntaxExceptionId : InternalExceptionId := arbitrary _

def throwPostpone {α m} [MonadExcept Exception m] : m α :=
throw $ Exception.internal postponeExceptionId

def throwUnsupportedSyntax {α m} [MonadExcept Exception m] : m α :=
throw $ Exception.internal unsupportedSyntaxExceptionId

def mkMessageCore (fileName : String) (fileMap : FileMap) (msgData : MessageData) (severity : MessageSeverity) (pos : String.Pos) : Message :=
let pos := fileMap.toPosition pos;
{ fileName := fileName, pos := pos, data := msgData, severity := severity }

end Elab
end Lean
