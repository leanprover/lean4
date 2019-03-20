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

structure sourceInfo :=
/- Will be inferred after parsing by `syntax.updateLeading`. During parsing,
   it is not at all clear what the preceding token was, especially with backtracking. -/
(leading  : substring)
(pos      : parsec.position)
(trailing : substring)

structure syntaxAtom :=
(info : option sourceInfo := none) (val : string)

/-- A simple wrapper that should remind you to use the static declaration instead
    of hard-coding the node name. -/
structure syntaxNodeKind :=
-- should be equal to the name of the declaration this structure instance was bound to
(name : name)

/-- Signifies ambiguous syntax to be disambiguated by the elaborator. Should have at least two children.

    This node kind is special-cased by `syntax.reprint` since its children's outputs should not be concatenated. -/
@[pattern] def choice : syntaxNodeKind := ⟨`lean.parser.choice⟩
/-- A nondescriptive kind that can be used for merely grouping syntax trees into a node.

    This node kind is special-cased by `syntax.format` to be printed as brackets `[...]` without a node kind. -/
@[pattern] def noKind : syntaxNodeKind := ⟨`lean.parser.noKind⟩

/-- A hygiene marker introduced by a macro expansion. -/
@[derive decidableEq hasToFormat]
def macroScope := nat
abbrev macroScopes := list macroScope

/-
Parsers create `syntaxNode`'s with the following properties (see implementation of `combinators.node`):
- If `args` contains a `syntax.missing`, then all subsequent elements are also `syntax.missing`.
- The first argument in `args` is not `syntax.missing`

Remark: We do create `syntaxNode`'s with an empty `args` field (e.g. for representing `option.none`).
-/
structure syntaxNode (syntax : Type) :=
(kind : syntaxNodeKind)
(args : list syntax)
-- Lazily propagated scopes. Scopes are pushed inwards when a node is destructed via `syntax.asNode`,
-- until an ident or an atom (in which the scopes vanish) is reached.
-- Scopes are stored in a stack with the most recent scope at the top.
(scopes : macroScopes := [])

structure syntaxIdent :=
(info : option sourceInfo := none)
(rawVal : substring)
(val : name)
/- A list of overloaded, global names that this identifier could have referred to in the lexical context
   where it was parsed.
   If the identifier does not resolve to a local binding, it should instead resolve to one of
   these preresolved constants. -/
(preresolved : list name := [])
(scopes : macroScopes := [])

inductive syntax
| atom (val : syntaxAtom)
| ident (val : syntaxIdent)
-- note: use `syntax.asNode` instead of matching against this constructor so that
-- macro scopes are propagated
| rawNode (val : syntaxNode syntax)
| missing

instance : inhabited syntax :=
⟨syntax.missing⟩

def substring.toString (s : substring) : string :=
s.start.extract s.stop

def substring.ofString (s : string) : substring :=
⟨s.mkIterator, s.mkIterator.toEnd⟩

instance substring.hasToString : hasToString substring :=
⟨substring.toString⟩

-- TODO(Sebastian): exhaustively argue why (if?) this is correct
-- The basic idea is list concatenation with elimination of adjacent identical scopes
def macroScopes.flip : macroScopes → macroScopes → macroScopes
| ys (x::xs) := (match macroScopes.flip ys xs with
  | y::ys := if x = y then ys else x::y::ys
  | []    := [x])
| ys []      := ys

namespace syntax
open lean.format

def flipScopes (scopes : macroScopes) : syntax → syntax
| (syntax.ident n) := syntax.ident {n with scopes := n.scopes.flip scopes}
| (syntax.rawNode n) := syntax.rawNode {n with scopes := n.scopes.flip scopes}
| stx := stx

def mkNode (kind : syntaxNodeKind) (args : list syntax) :=
syntax.rawNode { kind := kind, args := args }

/-- Match against `syntax.rawNode`, propagating lazy macro scopes. -/
def asNode : syntax → option (syntaxNode syntax)
| (syntax.rawNode n) := some {n with args := n.args.map (flipScopes n.scopes), scopes := []}
| _                   := none

protected def list (args : list syntax) :=
mkNode noKind args

def kind : syntax → option syntaxNodeKind
| (syntax.rawNode n) := some n.kind
| _                   := none

def isOfKind (k : syntaxNodeKind) : syntax → bool
| (syntax.rawNode n) := k.name = n.kind.name
| _ := ff

section
variables {m : Type → Type} [monad m] (r : syntax → m (option syntax))

mutual def mreplace, mreplaceLst
with mreplace : syntax → m syntax
| stx@(rawNode n) := do
  o ← r stx,
  (match o with
  | some stx' := pure stx'
  | none      := do args' ← mreplaceLst n.args, pure $ rawNode {n with args := args'})
| stx := do
  o ← r stx,
  pure $ o.getOrElse stx
with mreplaceLst : list syntax → m (list syntax)
| []      := pure []
| (s::ss) := list.cons <$> mreplace s <*> mreplaceLst ss

def replace := @mreplace id _
end

/- Remark: the state `string.iterator` is the `sourceInfo.trailing.stop` of the previous token,
   or the beginning of the string. -/
private def updateLeadingAux : syntax → state string.iterator (option syntax)
| (atom a@{info := some info, ..}) := do
  last ← get,
  put info.trailing.stop,
  pure $ some $ atom {a with info := some {info with leading := ⟨last, last.nextn (info.pos - last.offset)⟩}}
| (ident id@{info := some info, ..}) := do
  last ← get,
  put info.trailing.stop,
  pure $ some $ ident {id with info := some {info with leading := ⟨last, last.nextn (info.pos - last.offset)⟩}}
| _ := pure none

/-- Set `sourceInfo.leading` according to the trailing stop of the preceding token.
    The result is a round-tripping syntax tree IF, in the input syntax tree,
    * all leading stops, atom contents, and trailing starts are correct
    * trailing stops are between the trailing start and the next leading stop.

    Remark: after parsing all `sourceInfo.leading` fields are empty.
    The syntax argument is the output produced by the parser for `source`.
    This function "fixes" the `source.leanding` field.

    Note that, the `sourceInfo.trailing` fields are correct.
    The implementation of this function relies on this property. -/
def updateLeading (source : string) : syntax → syntax :=
λ stx, prod.fst $ (mreplace updateLeadingAux stx).run source.mkIterator

/-- Retrieve the left-most leaf's info in the syntax tree. -/
mutual def getHeadInfo, getHeadInfoLst
with getHeadInfo : syntax → option sourceInfo
| (atom a)   := a.info
| (ident id) := id.info
| (rawNode n) := getHeadInfoLst n.args
| _ := none
with getHeadInfoLst : list syntax → option sourceInfo
| [] := none
| (stx::stxs) := getHeadInfo stx <|> getHeadInfoLst stxs

def getPos (stx : syntax) : option parsec.position :=
do i ← stx.getHeadInfo,
   pure i.pos

def reprintAtom : syntaxAtom → string
| ⟨some info, s⟩ := info.leading.toString ++ s ++ info.trailing.toString
| ⟨none, s⟩      := s

mutual def reprint, reprintLst
with reprint : syntax → option string
| (atom ⟨some info, s⟩) := pure $ info.leading.toString ++ s ++ info.trailing.toString
| (atom ⟨none, s⟩)      := pure s
| (ident id@{info := some info, ..}) := pure $ info.leading.toString ++ id.rawVal.toString ++ info.trailing.toString
| (ident id@{info := none,      ..}) := pure id.rawVal.toString
| (rawNode n) :=
  if n.kind.name = choice.name then match n.args with
  -- should never happen
  | [] := failure
  -- check that every choice prints the same
  | n::ns := do
    s ← reprint n,
    ss ← reprintLst ns,
    guard $ ss.all (= s),
    pure s
  else string.join <$> reprintLst n.args
| missing := ""
with reprintLst : list syntax → option (list string)
| []      := pure []
| (n::ns) := do
  s ← reprint n,
  ss ← reprintLst ns,
  pure $ s::ss

protected mutual def toFormat, toFormatLst
with toFormat : syntax → format
| (atom ⟨_, s⟩) := toFmt $ repr s
| (ident id)    :=
  let scopes := id.preresolved.map toFmt ++ id.scopes.reverse.map toFmt in
  let scopes := match scopes with [] := toFmt "" | _ := bracket "{" (joinSep scopes ", ") "}" in
  toFmt "`" ++ toFmt id.val ++ scopes
| stx@(rawNode n) :=
  let scopes := match n.scopes with [] := toFmt "" | _ := bracket "{" (joinSep n.scopes.reverse ", ") "}" in
  if n.kind.name = `lean.parser.noKind then sbracket $ scopes ++ joinSep (toFormatLst n.args) line
  else let shorterName := n.kind.name.replacePrefix `lean.parser name.anonymous
       in paren $ joinSep ((toFmt shorterName ++ scopes) :: toFormatLst n.args) line
| missing := "<missing>"
with toFormatLst : list syntax → list format
| []      := []
| (s::ss) := toFormat s :: toFormatLst ss

instance : hasToFormat syntax := ⟨syntax.toFormat⟩
instance : hasToString syntax := ⟨toString ∘ toFmt⟩
end syntax

end parser
end lean
