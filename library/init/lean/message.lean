/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Message type used by the Lean frontend
-/
prelude
import init.data.toString init.lean.position

namespace lean
inductive messageSeverity
| information | warning | error

-- TODO: structured messages
structure message :=
(filename : string)
(pos      : position)
(endPos  : option position  := none)
(severity : messageSeverity := messageSeverity.error)
(caption  : string           := "")
(text     : string)

namespace message
protected def toString (msg : message) : string :=
msg.filename ++ ":" ++ toString msg.pos.line ++ ":" ++ toString msg.pos.column ++ ": " ++
(match msg.severity with
 | messageSeverity.information := ""
 | messageSeverity.warning := "warning: "
 | messageSeverity.error := "error: ") ++
(if msg.caption = "" then "" else msg.caption ++ ":\n") ++
msg.text

instance : hasToString message :=
⟨message.toString⟩
end message

structure messageLog :=
-- messages are stored in reverse for efficient append
(revList : list message)

namespace messageLog
def empty : messageLog :=
⟨[]⟩

def add (msg : message) (log : messageLog) : messageLog :=
⟨msg :: log.revList⟩

protected def append (l₁ l₂ : messageLog) : messageLog :=
⟨l₂.revList ++ l₁.revList⟩

instance : hasAppend messageLog :=
⟨messageLog.append⟩

def hasErrors (log : messageLog) : bool :=
log.revList.any $ λ m, match m.severity with
| messageSeverity.error := tt
| _                      := ff

def toList (log : messageLog) : list message :=
log.revList.reverse
end messageLog
end lean
