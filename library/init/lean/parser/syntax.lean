/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich
-/
prelude
import init.lean.name init.lean.parser.parsec

namespace lean
namespace parser

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
(info : option source_info := none) (val : string)

/-- A simple wrapper that should remind you to use the static declaration instead
    of hard-coding the node name. -/
structure syntax_node_kind :=
-- should be equal to the name of the declaration this structure instance was bound to
(name : name)

@[pattern] def choice : syntax_node_kind := ⟨`lean.parser.choice⟩
-- TODO(Sebastian): replace `option syntax_kind` using this special kind
@[pattern] def no_kind : syntax_node_kind := ⟨`lean.parser.no_kind⟩

/-
Parsers create `syntax_node`'s with the following properties (see implementation of `combinators.node`):
- If `args` contains a `syntax.missing`, then all subsequent elements are also `syntax.missing`.
- The first argument in `args` is not `syntax.missing`

Remark: We do create `syntax_node`'s with an empty `args` field (e.g. for representing `option.none`).
-/
structure syntax_node (syntax : Type) :=
-- TODO: add `lean.parser.list` kind, and remove option. Then `none` = `lean.parser.seq`
(kind : option syntax_node_kind) (args : list syntax)

inductive syntax
| atom (val : syntax_atom)
| node (val : syntax_node syntax)
| missing

instance : inhabited syntax :=
⟨syntax.missing⟩

def substring.to_string (s : substring) : string :=
(s.start.extract s.stop).get_or_else ""

namespace syntax
open lean.format

def is_of_kind (k : syntax_node_kind) : syntax → bool
| (syntax.node ⟨some k', _⟩) := k.name = k'.name
| _ := ff

-- Remark: this function must be updated whenever `ident` parser is modified.
-- This function was defined before we had the `ident` parser.
-- TODO: move it to the `ident` parser file and use the view defined there.
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
  if kind.name = `lean.parser.no_kind then sbracket $ join_sep (to_format_lst args) line
  else if kind.name = `lean.parser.ident then to_fmt "`" ++ ident_to_format stx
  else let shorter_name := kind.name.replace_prefix `lean.parser name.anonymous
       in paren $ join_sep (to_fmt shorter_name :: to_format_lst args) line
| missing := "<missing>"
with to_format_lst : list syntax → list format
| []      := []
| (s::ss) := to_format s :: to_format_lst ss

/- Remark: the state `string.iterator` is the `source_info.trailing.stop` of the previous token,
   or the beginning of the string. -/
private mutual def update_leading_aux, update_leading_lst
with update_leading_aux : syntax → state string.iterator syntax
| (atom a@{info := some info, ..}) := do
  last ← get,
  put info.trailing.stop,
  pure $ atom {a with info := some {info with leading := ⟨last, last.nextn (info.pos - last.offset)⟩}}
| (node n) := do args ← update_leading_lst n.args, pure $ node {n with args := args}
| stx := pure stx
with update_leading_lst : list syntax → state string.iterator (list syntax)
| []      := pure []
| (s::ss) := list.cons <$> update_leading_aux s <*> update_leading_lst ss

/-- Set `source_info.leading` according to the trailing stop of the preceding token.
    The result is a round-tripping syntax tree IF, in the input syntax tree,
    * all leading stops, atom contents, and trailing starts are correct
    * trailing stops are between the trailing start and the next leading stop.

    Remark: after parsing all `source_info.leading` fields are empty.
    The syntax argument is the output produced by the parser for `source`.
    This function "fixes" the `source.leanding` field.

    Note that, the `source_info.trailing` fields are correct.
    The implementation of this function relies on this property. -/
def update_leading (source : string) : syntax → syntax :=
λ stx, prod.fst $ (update_leading_aux stx).run source.mk_iterator

def is_empty_node : syntax → bool
| (node ⟨_, []⟩) := tt
| _              := ff

/-- Retrieve the left-most leaf in the syntax tree. -/
def get_head_atom : syntax → option syntax_atom
| (atom a) := some a
-- TODO: handle case where `n` is an empty `syntax_node`
-- We will have to create a mutual recursion here Arghhhh
| (node ⟨_, n::ns⟩) := n.get_head_atom
| _ := none

def get_pos (stx : syntax) : option parsec.position :=
do a ← stx.get_head_atom,
   i ← a.info,
   pure i.pos

def reprint_atom : syntax_atom → string
| ⟨some info, s⟩ := info.leading.to_string ++ s ++ info.trailing.to_string
| ⟨none, s⟩      := s

mutual def reprint, reprint_lst
with reprint : syntax → option string
| (atom a) := reprint_atom a
| (node ⟨some k, ns⟩) :=
  if k.name = choice.name then match ns with
  -- should never happen
  | [] := failure
  -- check that every choice prints the same
  | n::ns := do
    s ← reprint n,
    ss ← reprint_lst ns,
    guard $ ss.all (= s),
    pure s
  else string.join <$> reprint_lst ns
| (node ⟨_, ns⟩) := string.join <$> reprint_lst ns
| missing := ""
with reprint_lst : list syntax → option (list string)
| []      := pure []
| (n::ns) := do
  s ← reprint n,
  ss ← reprint_lst ns,
  pure $ s::ss
end syntax

instance : has_to_format syntax := ⟨syntax.to_format⟩
instance : has_to_string syntax := ⟨to_string ∘ to_fmt⟩

end parser
end lean
