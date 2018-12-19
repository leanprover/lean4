/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Message type used by the Lean frontend
-/
prelude
import init.data.to_string

namespace lean
structure position :=
(line column : nat)

inductive message_severity
| information | warning | error

-- TODO: structured messages
structure message :=
(filename : string)
(pos      : position)
(end_pos  : option position  := none)
(severity : message_severity := message_severity.error)
(caption  : string           := "")
(text     : string)

namespace message
protected def to_string (msg : message) : string :=
msg.filename ++ ":" ++ to_string msg.pos.line ++ ":" ++ to_string msg.pos.column ++ ": " ++
(match msg.severity with
 | message_severity.information := ""
 | message_severity.warning := "warning: "
 | message_severity.error := "error: ") ++
(if msg.caption = "" then "" else msg.caption ++ ":\n") ++
msg.text

instance : has_to_string message :=
⟨message.to_string⟩
end message

structure message_log :=
-- messages are stored in reverse for efficient append
(rev_list : list message)

namespace message_log
def empty : message_log :=
⟨[]⟩

def add (msg : message) (log : message_log) : message_log :=
⟨msg :: log.rev_list⟩

protected def append (l₁ l₂ : message_log) : message_log :=
⟨l₂.rev_list ++ l₁.rev_list⟩

instance : has_append message_log :=
⟨message_log.append⟩

def has_errors (log : message_log) : bool :=
log.rev_list.any $ λ m, match m.severity with
| message_severity.error := tt
| _                      := ff

def to_list (log : message_log) : list message :=
log.rev_list.reverse
end message_log
end lean
