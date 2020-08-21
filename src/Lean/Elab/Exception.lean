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

inductive Exception
| core (ex : Core.Exception)
| unsupportedSyntax

instance Exception.inhabited : Inhabited Exception := ⟨Exception.unsupportedSyntax⟩

instance Exception.hasToString : HasToString Exception :=
⟨fun ex => match ex with
 | Exception.core ex           => toString ex
 | Exception.unsupportedSyntax => "unsupported syntax"⟩

def mkMessageCore (fileName : String) (fileMap : FileMap) (msgData : MessageData) (severity : MessageSeverity) (pos : String.Pos) : Message :=
let pos := fileMap.toPosition pos;
{ fileName := fileName, pos := pos, data := msgData, severity := severity }

-- def mkExceptionCore (fileName : String) (fileMap : FileMap) (msgData : MessageData) (pos : String.Pos) : Exception :=
-- let pos := fileMap.toPosition pos;
-- Exception.error { fileName := fileName, pos := pos, data := msgData, severity := MessageSeverity.error }

end Elab
end Lean
