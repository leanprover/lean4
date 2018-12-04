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

/-- Signifies ambiguous syntax to be disambiguated by the elaborator. Should have at least two children.

    This node kind is special-cased by `syntax.reprint` since its children's outputs should not be concatenated. -/
@[pattern] def choice : syntax_node_kind := ⟨`lean.parser.choice⟩
/-- A nondescriptive kind that can be used for merely grouping syntax trees into a node.

    This node kind is special-cased by `syntax.format` to be printed as brackets `[...]` without a node kind. -/
@[pattern] def no_kind : syntax_node_kind := ⟨`lean.parser.no_kind⟩

/-- A hygiene marker introduced by a macro expansion. -/
@[derive decidable_eq has_to_format]
def macro_scope := nat
abbreviation macro_scopes := list macro_scope

/-
Parsers create `syntax_node`'s with the following properties (see implementation of `combinators.node`):
- If `args` contains a `syntax.missing`, then all subsequent elements are also `syntax.missing`.
- The first argument in `args` is not `syntax.missing`

Remark: We do create `syntax_node`'s with an empty `args` field (e.g. for representing `option.none`).
-/
structure syntax_node (syntax : Type) :=
(kind : syntax_node_kind)
(args : list syntax)
-- Lazily propagated scopes. Scopes are pushed inwards when a node is destructed via `syntax.as_node`,
-- until an ident or an atom (in which the scopes vanish) is reached
(scopes : macro_scopes := [])

structure syntax_ident :=
(info : option source_info := none)
(raw_val : substring)
(val : name)
/- A list of overloaded, global names that this identifier could have referred to in the lexical context
   where it was parsed.
   If the identifier does not resolve to a local binding, it should instead resolve to one of
   these preresolved constants. -/
(preresolved : list name := [])
(scopes : macro_scopes := [])

inductive syntax
| atom (val : syntax_atom)
| ident (val : syntax_ident)
-- note: use `syntax.as_node` instead of matching against this constructor so that
-- macro scopes are propagated
| raw_node (val : syntax_node syntax)
| missing

instance : inhabited syntax :=
⟨syntax.missing⟩

def substring.to_string (s : substring) : string :=
(s.start.extract s.stop).get_or_else ""

def substring.of_string (s : string) : substring :=
⟨s.mk_iterator, s.mk_iterator.to_end⟩

instance substring.has_to_string : has_to_string substring :=
⟨substring.to_string⟩

-- TODO(Sebastian): exhaustively argue why (if?) this is correct
def macro_scopes.flip : macro_scopes → macro_scopes → macro_scopes
| (x::xs) (y::ys) := if x = y then macro_scopes.flip xs ys else (y::ys) ++ (x::xs)
| []      ys      := ys
| xs      []      := xs

namespace syntax
open lean.format

def flip_scopes (scopes : macro_scopes) : syntax → syntax
| (syntax.ident n) := syntax.ident {n with scopes := n.scopes.flip scopes}
| (syntax.raw_node n) := syntax.raw_node {n with scopes := n.scopes.flip scopes}
| stx := stx

def mk_node (kind : syntax_node_kind) (args : list syntax) :=
syntax.raw_node { kind := kind, args := args }

/-- Match against `syntax.raw_node`, propagating lazy macro scopes. -/
def as_node : syntax → option (syntax_node syntax)
| (syntax.raw_node n) := some {n with args := n.args.map (flip_scopes n.scopes), scopes := []}
| _                   := none

protected def list (args : list syntax) :=
mk_node no_kind args

def kind : syntax → option syntax_node_kind
| (syntax.raw_node n) := some n.kind
| _                   := none

def is_of_kind (k : syntax_node_kind) : syntax → bool
| (syntax.raw_node n) := k.name = n.kind.name
| _ := ff

/- Remark: the state `string.iterator` is the `source_info.trailing.stop` of the previous token,
   or the beginning of the string. -/
private mutual def update_leading_aux, update_leading_lst
with update_leading_aux : syntax → state string.iterator syntax
| (atom a@{info := some info, ..}) := do
  last ← get,
  put info.trailing.stop,
  pure $ atom {a with info := some {info with leading := ⟨last, last.nextn (info.pos - last.offset)⟩}}
| (ident id@{info := some info, ..}) := do
  last ← get,
  put info.trailing.stop,
  pure $ ident {id with info := some {info with leading := ⟨last, last.nextn (info.pos - last.offset)⟩}}
| (raw_node n) := do args ← update_leading_lst n.args, pure $ raw_node {n with args := args}
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

/-- Retrieve the left-most leaf's info in the syntax tree. -/
def get_head_info : syntax → option source_info
| (atom a)   := a.info
| (ident id) := id.info
-- TODO: handle case where `n` is an empty `syntax_node`
-- We will have to create a mutual recursion here Arghhhh
| (raw_node {args:=n::ns, ..}) := n.get_head_info
| _ := none

def get_pos (stx : syntax) : option parsec.position :=
do i ← stx.get_head_info,
   pure i.pos

def reprint_atom : syntax_atom → string
| ⟨some info, s⟩ := info.leading.to_string ++ s ++ info.trailing.to_string
| ⟨none, s⟩      := s

mutual def reprint, reprint_lst
with reprint : syntax → option string
| (atom ⟨some info, s⟩) := pure $ info.leading.to_string ++ s ++ info.trailing.to_string
| (atom ⟨none, s⟩)      := pure s
| (ident id@{info := some info, ..}) := pure $ info.leading.to_string ++ id.raw_val.to_string ++ info.trailing.to_string
| (ident id@{info := none,      ..}) := pure id.raw_val.to_string
| (raw_node n) :=
  if n.kind.name = choice.name then match n.args with
  -- should never happen
  | [] := failure
  -- check that every choice prints the same
  | n::ns := do
    s ← reprint n,
    ss ← reprint_lst ns,
    guard $ ss.all (= s),
    pure s
  else string.join <$> reprint_lst n.args
| missing := ""
with reprint_lst : list syntax → option (list string)
| []      := pure []
| (n::ns) := do
  s ← reprint n,
  ss ← reprint_lst ns,
  pure $ s::ss

protected mutual def to_format, to_format_lst
with to_format : syntax → format
| (atom ⟨_, s⟩) := to_fmt $ repr s
| (ident id)    := to_fmt "`" ++ to_fmt id.val
| stx@(raw_node n) :=
  let scopes := match n.scopes with [] := to_fmt "" | _ := bracket "{" (join_sep n.scopes ", ") "}" in
  if n.kind.name = `lean.parser.no_kind then sbracket $ scopes ++ join_sep (to_format_lst n.args) line
  else let shorter_name := n.kind.name.replace_prefix `lean.parser name.anonymous
       in paren $ join_sep ((to_fmt shorter_name ++ scopes) :: to_format_lst n.args) line
| missing := "<missing>"
with to_format_lst : list syntax → list format
| []      := []
| (s::ss) := to_format s :: to_format_lst ss

instance : has_to_format syntax := ⟨syntax.to_format⟩
instance : has_to_string syntax := ⟨to_string ∘ to_fmt⟩
end syntax

end parser
end lean
