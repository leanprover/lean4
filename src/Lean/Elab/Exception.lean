/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Init.System.IOError
import Lean.Meta.Message

namespace Lean
namespace Elab

inductive Exception
| error (msg : Message)
| io (err : IO.Error)
| unsupportedSyntax

@[inline] instance Exception.monadIO : MonadIO (EIO Exception) :=
mkEIOMonadIO Exception.io

instance Exception.inhabited : Inhabited Exception := ⟨Exception.error $ arbitrary _⟩

instance Exception.hasToString : HasToString Exception :=
⟨fun ex => match ex with
 | Exception.error msg         => toString msg
 | Exception.io err            => toString err
 | Exception.unsupportedSyntax => "unsupported syntax"⟩

def mkMessageCore (fileName : String) (fileMap : FileMap) (msgData : MessageData) (severity : MessageSeverity) (pos : String.Pos) : Message :=
let pos := fileMap.toPosition pos;
{ fileName := fileName, pos := pos, data := msgData, severity := severity }

def mkExceptionCore (fileName : String) (fileMap : FileMap) (msgData : MessageData) (pos : String.Pos) : Exception :=
let pos := fileMap.toPosition pos;
Exception.error { fileName := fileName, pos := pos, data := msgData, severity := MessageSeverity.error }

end Elab
end Lean
