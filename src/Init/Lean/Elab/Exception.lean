/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta

namespace Lean
namespace Elab

abbrev Exception := Message

def mkMessageCore (fileName : String) (fileMap : FileMap) (msgData : MessageData) (severity : MessageSeverity) (pos : String.Pos) : Message :=
let pos := fileMap.toPosition pos;
{ fileName := fileName, pos := pos, data := msgData, severity := severity }

def mkExceptionCore (fileName : String) (fileMap : FileMap) (msgData : MessageData) (pos : String.Pos) : Exception :=
let pos := fileMap.toPosition pos;
{ fileName := fileName, pos := pos, data := msgData, severity := MessageSeverity.error }

end Elab
end Lean
