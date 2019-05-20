/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich
-/
prelude
import init.lean.name init.lean.parser.parsec

namespace Lean
namespace Parser

--TODO(Sebastian): move
structure Substring :=
(start : String.OldIterator)
(stop : String.OldIterator)

structure SourceInfo :=
/- Will be inferred after parsing by `Syntax.updateLeading`. During parsing,
   it is not at all clear what the preceding token was, especially with backtracking. -/
(leading  : Substring)
(pos      : Parsec.Position)
(trailing : Substring)

structure SyntaxAtom :=
(info : Option SourceInfo := none) (val : String)

/-- A simple wrapper that should remind you to use the static declaration instead
    of hard-coding the Node Name. -/
structure SyntaxNodeKind :=
-- should be equal to the Name of the declaration this structure instance was bound to
(name : Name)

/-- Signifies ambiguous Syntax to be disambiguated by the Elaborator. Should have at least two children.

    This Node kind is special-cased by `Syntax.reprint` since its children's outputs should not be concatenated. -/
@[pattern] def choice : SyntaxNodeKind := ⟨`Lean.Parser.choice⟩
/-- A nondescriptive kind that can be used for merely grouping Syntax trees into a Node.

    This Node kind is special-cased by `Syntax.Format` to be printed as brackets `[...]` without a Node kind. -/
@[pattern] def noKind : SyntaxNodeKind := ⟨`Lean.Parser.noKind⟩

/-- A hygiene marker introduced by a macro expansion. -/
@[derive DecidableEq HasFormat]
def MacroScope := Nat
abbrev macroScopes := List MacroScope

/-
Parsers create `SyntaxNode`'s with the following properties (see implementation of `Combinators.Node`):
- If `args` contains a `Syntax.missing`, then all subsequent elements are also `Syntax.missing`.
- The first argument in `args` is not `Syntax.missing`

Remark: We do create `SyntaxNode`'s with an Empty `args` field (e.g. for representing `Option.none`).
-/
structure SyntaxNode (Syntax : Type) :=
(kind : SyntaxNodeKind)
(args : List Syntax)
-- Lazily propagated scopes. Scopes are pushed inwards when a Node is destructed via `Syntax.asNode`,
-- until an ident or an atom (in which the scopes vanish) is reached.
-- Scopes are stored in a stack with the most recent Scope at the top.
(scopes : macroScopes := [])

structure SyntaxIdent :=
(info : Option SourceInfo := none)
(rawVal : Substring)
(val : Name)
/- A List of overloaded, global names that this identifier could have referred to in the lexical context
   where it was parsed.
   If the identifier does not resolve to a local binding, it should instead resolve to one of
   these preresolved constants. -/
(preresolved : List Name := [])
(scopes : macroScopes := [])

inductive Syntax
| atom (val : SyntaxAtom)
| ident (val : SyntaxIdent)
-- note: use `Syntax.asNode` instead of matching against this Constructor so that
-- macro scopes are propagated
| rawNode (val : SyntaxNode Syntax)
| missing

instance : Inhabited Syntax :=
⟨Syntax.missing⟩

def Substring.toString (s : Substring) : String :=
s.start.extract s.stop

def Substring.ofString (s : String) : Substring :=
⟨s.mkOldIterator, s.mkOldIterator.toEnd⟩

instance Substring.HasToString : HasToString Substring :=
⟨Substring.toString⟩

-- TODO(Sebastian): exhaustively argue why (if?) this is correct
-- The basic idea is List concatenation with elimination of adjacent identical scopes
def macroScopes.flip : macroScopes → macroScopes → macroScopes
| ys (x::xs) := match macroScopes.flip ys xs with
  | y::ys := if x = y then ys else x::y::ys
  | []    := [x]
| ys []      := ys

namespace Syntax
open Lean.Format

def flipScopes (scopes : macroScopes) : Syntax → Syntax
| (Syntax.ident n) := Syntax.ident {n with scopes := n.scopes.flip scopes}
| (Syntax.rawNode n) := Syntax.rawNode {n with scopes := n.scopes.flip scopes}
| stx := stx

def mkNode (kind : SyntaxNodeKind) (args : List Syntax) :=
Syntax.rawNode { kind := kind, args := args }

/-- Match against `Syntax.rawNode`, propagating lazy macro scopes. -/
def asNode : Syntax → Option (SyntaxNode Syntax)
| (Syntax.rawNode n) := some {n with args := n.args.map (flipScopes n.scopes), scopes := []}
| _                   := none

protected def list (args : List Syntax) :=
mkNode noKind args

def kind : Syntax → Option SyntaxNodeKind
| (Syntax.rawNode n) := some n.kind
| _                   := none

def isOfKind (k : SyntaxNodeKind) : Syntax → Bool
| (Syntax.rawNode n) := k.name = n.kind.name
| _ := false

section
variables {m : Type → Type} [Monad m] (r : Syntax → m (Option Syntax))

partial def mreplace : Syntax → m Syntax
| stx@(rawNode n) := do
  o ← r stx,
  match o with
  | some stx' := pure stx'
  | none      := do args' ← n.args.mmap mreplace, pure $ rawNode {n with args := args'}
| stx := do
  o ← r stx,
  pure $ o.getOrElse stx

def replace := @mreplace Id _
end

/- Remark: the State `String.Iterator` is the `SourceInfo.trailing.stop` of the previous token,
   or the beginning of the String. -/
private def updateLeadingAux : Syntax → State String.OldIterator (Option Syntax)
| (atom a@{info := some info, ..}) := do
  last ← get,
  set info.trailing.stop,
  pure $ some $ atom {a with info := some {info with leading := ⟨last, last.nextn (info.pos - last.offset)⟩}}
| (ident id@{info := some info, ..}) := do
  last ← get,
  set info.trailing.stop,
  pure $ some $ ident {id with info := some {info with leading := ⟨last, last.nextn (info.pos - last.offset)⟩}}
| _ := pure none

/-- Set `SourceInfo.leading` according to the trailing stop of the preceding token.
    The Result is a round-tripping Syntax tree IF, in the input Syntax tree,
    * all leading stops, atom contents, and trailing starts are correct
    * trailing stops are between the trailing start and the next leading stop.

    Remark: after parsing all `SourceInfo.leading` fields are Empty.
    The Syntax argument is the output produced by the Parser for `source`.
    This Function "fixes" the `source.leanding` field.

    Note that, the `SourceInfo.trailing` fields are correct.
    The implementation of this Function relies on this property. -/
def updateLeading (source : String) : Syntax → Syntax :=
λ stx, Prod.fst $ (mreplace updateLeadingAux stx).run source.mkOldIterator

/-- Retrieve the left-most leaf's info in the Syntax tree. -/
partial def getHeadInfo : Syntax → Option SourceInfo
| (atom a)    := a.info
| (ident id)  := id.info
| (rawNode n) := n.args.foldr (λ s r, getHeadInfo s <|> r) none
| _           := none

def getPos (stx : Syntax) : Option Parsec.Position :=
do i ← stx.getHeadInfo,
   pure i.pos

def reprintAtom : SyntaxAtom → String
| ⟨some info, s⟩ := info.leading.toString ++ s ++ info.trailing.toString
| ⟨none, s⟩      := s

partial def reprint : Syntax → Option String
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
    ss ← ns.mmap reprint,
    guard $ ss.all (= s),
    pure s
  else String.join <$> n.args.mmap reprint
| missing := ""

protected partial def format : Syntax → Format
| (atom ⟨_, s⟩) := fmt $ repr s
| (ident id)    :=
  let scopes := id.preresolved.map fmt ++ id.scopes.reverse.map fmt in
  let scopes := match scopes with [] := fmt "" | _ := bracket "{" (joinSep scopes ", ") "}" in
  fmt "`" ++ fmt id.val ++ scopes
| stx@(rawNode n) :=
  let scopes := match n.scopes with [] := fmt "" | _ := bracket "{" (joinSep n.scopes.reverse ", ") "}" in
  if n.kind.name = `Lean.Parser.noKind then sbracket $ scopes ++ joinSep (n.args.map format) line
  else let shorterName := n.kind.name.replacePrefix `Lean.Parser Name.anonymous
       in paren $ joinSep ((fmt shorterName ++ scopes) :: n.args.map format) line
| missing := "<missing>"

instance : HasFormat Syntax := ⟨Syntax.format⟩
instance : HasToString Syntax := ⟨toString ∘ fmt⟩
end Syntax

end Parser
end Lean
