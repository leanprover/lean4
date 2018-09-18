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
/- Will be inferred after parsing by `syntax.update_leading`. During parsing,
   it is not at all clear what the preceding token was, especially with backtracking. -/
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

private def ident_to_format : syntax → format
| stx := option.get_or_else (do
  syntax.node ⟨_, [syntax.node ⟨_, [syntax.node ⟨some ⟨idx⟩, part⟩]⟩, suffix]⟩ ← pure stx | failure,
  part ← match idx, part with
  | name.mk_numeral name.anonymous 0, [syntax.node ⟨_, [_, syntax.atom ⟨_, s⟩, _]⟩] := pure $ to_fmt "«" ++ s ++ "»"
  | name.mk_numeral name.anonymous 1, [syntax.atom ⟨_, s⟩] := pure $ s
  | _, _ := failure,
  match suffix with
  | syntax.node ⟨_, []⟩ := pure $ to_fmt part
  | syntax.node ⟨_, [syntax.node ⟨_, [_, id]⟩]⟩ := pure $ to_fmt part ++ "." ++ ident_to_format id
  | _ := failure
) "syntax.to_format: unexpected `ident` node content"

protected mutual def to_format, to_format_lst
with to_format : syntax → format
| (atom ⟨_, s⟩) := to_fmt $ repr s
| (node {kind := none, args := args, ..}) :=
  sbracket $ join_sep (to_format_lst args) line
| stx@(node {kind := some kind, args := args, ..}) :=
  if kind.name = `lean.parser.ident
  then to_fmt "`" ++ ident_to_format stx
  else paren $ join_sep (to_fmt (kind.name.replace_prefix `lean.parser name.anonymous) :: to_format_lst args) line
| missing := "<missing>"
with to_format_lst : list syntax → list format
| []      := []
| (s::ss) := to_format s :: to_format_lst ss

private mutual def update_leading_aux, update_leading_lst
with update_leading_aux : syntax → reader_t string (state string.iterator) syntax
| (atom a@{info := some info, ..}) := do
  source ← read,
  last ← get,
  put info.trailing.stop,
  pure $ atom {a with info := some {info with leading := ⟨last, source.mk_iterator.nextn info.pos⟩}}
| (node n) := do args ← update_leading_lst n.args, pure $ node {n with args := args}
| stx := pure stx
with update_leading_lst : list syntax → reader_t string (state string.iterator) (list syntax)
| []      := pure []
| (s::ss) := list.cons <$> update_leading_aux s <*> update_leading_lst ss

/-- Set `source_info.leading` according to the trailing stop of the preceding token.
    The result is a round-tripping syntax tree IF, in the input syntax tree,
    * all leading stops, atom contents, and trailing starts are correct
    * trailing stops are between the trailing start and the next leading stop. -/
def update_leading (source : string) : syntax → syntax :=
λ stx, prod.fst $ ((update_leading_aux stx).run source).run source.mk_iterator

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
