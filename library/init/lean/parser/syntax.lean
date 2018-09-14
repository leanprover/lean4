/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich
-/
prelude
import init.lean.name init.lean.parser.parsec

namespace lean
namespace parser

/-- De Bruijn index relative to surrounding 'bind' macros -/
@[reducible] def var_offset := ℕ
@[reducible] def macro_scope_id := ℕ

--TODO(Sebastian): move
structure substring :=
(start : string.iterator)
(stop : string.iterator)

structure source_info :=
(leading  : substring)
(pos      : parsec.position)
(trailing : substring)

structure syntax_atom :=
(info : option source_info) (val : string)

/-- A simple wrapper that should remind you to use the static declaration instead
    of hard-coding the node name. -/
structure syntax_node_kind :=
-- should be equal to the name of the declaration this structure instance was bound to
(name : name)

structure syntax_node (syntax : Type) :=
(kind : option syntax_node_kind) (args : list syntax)

inductive syntax
/- any non-ident atom -/
| atom (val : syntax_atom)
| node (val : syntax_node syntax)
| missing

instance : inhabited syntax :=
⟨syntax.missing⟩

instance coe_string_syntax : has_coe string syntax :=
⟨λ s, syntax.atom ⟨none, s⟩⟩

def substring.to_string (s : substring) : string :=
(s.start.extract s.stop).get_or_else ""

namespace syntax
open lean.format

protected mutual def to_format, to_format_lst
with to_format : syntax → format
| (atom ⟨_, s⟩) := to_fmt $ repr s
| (node {kind := none, args := args, ..}) :=
  sbracket $ join_sep (to_format_lst args) line
| (node {kind := some kind, args := args, ..}) :=
  paren $ join_sep (to_fmt kind.name :: to_format_lst args) line
| missing := "<missing>"
with to_format_lst : list syntax → list format
| []      := []
| (s::ss) := to_format s :: to_format_lst ss

def reprint_with_info : option source_info → string → string
| (some info) inner := info.leading.to_string ++ inner ++ info.trailing.to_string
| none        inner := inner

mutual def reprint, reprint_lst
with reprint : syntax → string
| (atom ⟨info, s⟩) := reprint_with_info info s
| (node n) := reprint_lst n.args
| missing := ""
with reprint_lst : list syntax → string
| []      := ""
| (s::ss) := reprint s ++ reprint_lst ss
end syntax

instance : has_to_format syntax := ⟨syntax.to_format⟩
instance : has_to_string syntax := ⟨to_string ∘ to_fmt⟩

end parser
end lean
