/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.Message

namespace Lean
namespace Elab

inductive Exception
| error             : Message → Exception
| unsupportedSyntax : Exception

instance Exception.inhabited : Inhabited Exception := ⟨Exception.error $ arbitrary _⟩

instance Exception.hasToString : HasToString Exception :=
⟨fun ex => match ex with
 | Exception.error msg         => toString msg
 | Exception.unsupportedSyntax => "unsupported syntax"⟩

def mkMessageCore (fileName : String) (fileMap : FileMap) (msgData : MessageData) (severity : MessageSeverity) (pos : String.Pos) : Message :=
let pos := fileMap.toPosition pos;
{ fileName := fileName, pos := pos, data := msgData, severity := severity }

def mkExceptionCore (fileName : String) (fileMap : FileMap) (msgData : MessageData) (pos : String.Pos) : Exception :=
let pos := fileMap.toPosition pos;
Exception.error { fileName := fileName, pos := pos, data := msgData, severity := MessageSeverity.error }

end Elab
end Lean
