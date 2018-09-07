/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Message type used by the Lean frontend
-/
prelude
import init.data.string.basic

namespace lean
structure position :=
(line column : nat)

inductive message_severity
| information | warning | error

structure message :=
(filename : string)
(pos      : position)
(end_pos  : option position  := none)
(severity : message_severity := message_severity.error)
(caption  : string           := "")
(text     : string)

def message_log := list message

namespace message_log
def add : message → message_log → message_log :=
list.cons

def has_errors (log : message_log) : bool :=
log.any $ λ m, match m.severity with
| message_severity.error := tt
| _                      := ff
end message_log
end lean
