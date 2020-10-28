/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich, Leonardo de Moura
-/
prelude
import init.lean.name init.lean.format init.data.array
-- set_option trace.compiler.ir.borrow true
-- namespace Lean
namespace Parser
open Lean

/-- A hygiene marker introduced by a macro expansion. -/
@[derive DecidableEq HasFormat]
def MacroScope := Nat
abbrev MacroScopes := List MacroScope

structure SourceInfo :=
/- Will be inferred after parsing by `Syntax.updateLeading`. During parsing,
   it is not at all clear what the preceding token was, especially with backtracking. -/
(leading  : Substring)
(pos      : String.Pos)
(trailing : Substring)

def SourceInfo.updateTrailing : SourceInfo → Substring → SourceInfo
| ⟨leading, pos, _⟩ trailing := ⟨leading, pos, trailing⟩

/- Node kind generation -/

def mkUniqIdRef : IO (IO.Ref Nat) :=
IO.mkRef 0

@[init mkUniqIdRef]
constant nextUniqId : IO.Ref Nat := default _

structure SyntaxNodeKind :=
(name : Name) (id : Nat)

instance stxKindInh : Inhabited SyntaxNodeKind :=
⟨{name := default _, id := default _}⟩

instance stxKindBeq : BEq SyntaxNodeKind :=
⟨λ k₁ k₂, k₁.id == k₂.id⟩

def mkNameToKindTable : IO (IO.Ref (NameMap Nat)) :=
IO.mkRef {}

@[init mkNameToKindTable]
constant nameToKindTable : IO.Ref (NameMap Nat) := default _

def nextKind (k : Name) : IO SyntaxNodeKind :=
do m ← nameToKindTable.get,
   when (m.contains k) (throw $ IO.userError ("kind '" ++ toString k ++ "' already exists")),
   id ← nextUniqId.get,
   nameToKindTable.set (m.insert k id),
   nextUniqId.set (id+1),
   pure { name := k, id := id }

/- Basic node kinds -/

def mkNullKind : IO SyntaxNodeKind := nextKind `null
@[init mkNullKind] constant nullKind : SyntaxNodeKind := default _
def mkChoiceKind : IO SyntaxNodeKind := nextKind `choice
@[init mkChoiceKind] constant choiceKind : SyntaxNodeKind := default _
def mkOptionSomeKind : IO SyntaxNodeKind := nextKind `some
@[init mkOptionSomeKind] constant optionSomeKind : SyntaxNodeKind := default _
def mkOptionNoneKind : IO SyntaxNodeKind := nextKind `none
@[init mkOptionNoneKind] constant optionNoneKind : SyntaxNodeKind := default _
def mkManyKind : IO SyntaxNodeKind := nextKind `many
@[init mkManyKind] constant manyKind : SyntaxNodeKind := default _
def mkHoleKind : IO SyntaxNodeKind := nextKind `hole

/- Syntax AST -/

inductive Syntax
| missing
| node   (kind : SyntaxNodeKind) (args : Array Syntax) (scopes : MacroScopes)
| atom   (info : Option SourceInfo) (val : String)
| ident  (info : Option SourceInfo) (rawVal : Substring) (val : Name) (preresolved : List Name) (scopes : MacroScopes)

instance stxInh : Inhabited Syntax :=
⟨Syntax.missing⟩

def SyntaxNodeKind.fix : SyntaxNodeKind → IO SyntaxNodeKind
| {name := n, ..} := do
  m ← nameToKindTable.get,
  match m.find n with
  | some id := pure {name := n, id := id}
  | none    := throw $ IO.userError ("Error unknown Syntax kind '" ++ toString n ++ "'")

partial def Syntax.fixKinds : Syntax → IO Syntax
| (Syntax.node k args scopes) := do
  k ← k.fix,
  args ← args.mmap Syntax.fixKinds,
  pure (Syntax.node k args scopes)
| other                       := pure other

inductive IsNode : Syntax → Prop
| mk (kind : SyntaxNodeKind) (args : Array Syntax) (scopes : MacroScopes) : IsNode (Syntax.node kind args scopes)

def SyntaxNode : Type := {s : Syntax // IsNode s }

def notIsNodeMissing (h : IsNode Syntax.missing) : False                   := match h with end
def notIsNodeAtom   {info val} (h : IsNode (Syntax.atom info val)) : False := match h with end
def notIsNodeIdent  {info rawVal val preresolved scopes} (h : IsNode (Syntax.ident info rawVal val preresolved scopes)) : False := match h with end

def unreachIsNodeMissing {α : Type} (h : IsNode Syntax.missing) : α := False.elim (notIsNodeMissing h)
def unreachIsNodeAtom {α : Type} {info val} (h : IsNode (Syntax.atom info val)) : α := False.elim (notIsNodeAtom h)
def unreachIsNodeIdent {α : Type} {info rawVal val preresolved scopes} (h : IsNode (Syntax.ident info rawVal val preresolved scopes)) : α :=
False.elim (match h with end)

@[inline] def withArgs {α : Type} (n : SyntaxNode) (fn : Array Syntax → α) : α :=
match n with
| ⟨Syntax.node _ args _, _⟩   := fn args
| ⟨Syntax.missing, h⟩         := unreachIsNodeMissing h
| ⟨Syntax.atom _ _, h⟩        := unreachIsNodeAtom h
| ⟨Syntax.ident _ _ _ _ _, h⟩ := unreachIsNodeIdent h

@[inline] def updateArgs (n : SyntaxNode) (fn : Array Syntax → Array Syntax) : Syntax :=
match n with
| ⟨Syntax.node kind args scopes, _⟩ := Syntax.node kind (fn args) scopes
| ⟨Syntax.missing, h⟩               := unreachIsNodeMissing h
| ⟨Syntax.atom _ _, h⟩              := unreachIsNodeAtom h
| ⟨Syntax.ident _ _ _ _ _, h⟩       := unreachIsNodeIdent h

-- TODO(Sebastian): exhaustively argue why (if?) this is correct
-- The basic idea is List concatenation with elimination of adjacent identical scopes
def MacroScopes.flip : MacroScopes → MacroScopes → MacroScopes
| ys []      := ys
| ys (x::xs) := match MacroScopes.flip ys xs with
  | y::ys := if x == y then ys else x::y::ys
  | []    := [x]

namespace Syntax
def isIdent : Syntax → Bool
| (Syntax.ident _ _ _ _ _) := true
| _                        := false

def isOfKind : Syntax → SyntaxNodeKind → Bool
| (Syntax.node kind _ _) k := k == kind
| other                  _ := false

def flipScopes (scopes : MacroScopes) : Syntax → Syntax
| (Syntax.ident info rawVal val pre scopes) := Syntax.ident info rawVal val pre (scopes.flip scopes)
| (Syntax.node kind args scopes)            := Syntax.node kind args (scopes.flip scopes)
| other := other

@[inline] def toSyntaxNode {α : Type} (s : Syntax) (base : α) (fn : SyntaxNode → α) : α :=
match s with
| Syntax.node kind args []     := fn ⟨Syntax.node kind args [], IsNode.mk _ _ _⟩
| Syntax.node kind args scopes := fn ⟨Syntax.node kind (args.map (flipScopes scopes)) [], IsNode.mk _ _ _⟩
| other                        := base

local attribute [instance] monadInhabited

@[specialize] partial def mreplace {m : Type → Type} [Monad m] (fn : Syntax → m (Option Syntax)) : Syntax → m Syntax
| stx@(node kind args scopes) := do
  o ← fn stx,
  (match o with
  | some stx := pure stx
  | none     := do args ← args.mmap mreplace, pure (node kind args scopes))
| stx := do o ← fn stx, pure (o.getOrElse stx)

@[inline] def replace {m : Type → Type} [Monad m] (fn : Syntax → m (Option Syntax)) := @mreplace Id _

private def updateInfo : SourceInfo → String.Pos → SourceInfo
| {leading := {str := s, startPos := _, stopPos := _}, pos := pos, trailing := trailing} last :=
  {leading := {str := s, startPos := last, stopPos := pos}, pos := pos, trailing := trailing}

/- Remark: the State `String.Pos` is the `SourceInfo.trailing.endPos` of the previous token,
   or the beginning of the String. -/
@[inline]
private def updateLeadingAux : Syntax → State String.Pos (Option Syntax)
| (atom (some info) val) := do
  last ← get,
  set info.trailing.stopPos,
  let newInfo := updateInfo info last in
  pure $ some (atom (some newInfo) val)
| (ident (some info) rawVal val pre scopes) := do
  last ← get,
  set info.trailing.stopPos,
  let newInfo := updateInfo info last in
  pure $ some (ident (some newInfo) rawVal val pre scopes)
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
def updateLeading : Syntax → Syntax :=
λ stx, Prod.fst <$> (mreplace updateLeadingAux stx).run 0

partial def updateTrailing (trailing : Substring) : Syntax → Syntax
| (Syntax.atom (some info) val)                     := Syntax.atom (some (info.updateTrailing trailing)) val
| (Syntax.ident (some info) rawVal val pre scopes)  := Syntax.ident (some (info.updateTrailing trailing)) rawVal val pre scopes
| n@(Syntax.node k args scopes)                     :=
  if args.size == 0 then n
  else
   let i    := args.size - 1 in
   let last := updateTrailing (args.get i) in
   let args := args.set i last in
   Syntax.node k args scopes
| other := other

/-- Retrieve the left-most leaf's info in the Syntax tree. -/
partial def getHeadInfo : Syntax → Option SourceInfo
| (atom info _)         := info
| (ident info _ _ _ _ ) := info
| (node _ args _)       := args.find getHeadInfo
| _                     := none

def getPos (stx : Syntax) : Option String.Pos :=
SourceInfo.pos <$> stx.getHeadInfo

private def reprintLeaf : Option SourceInfo → String → String
| none        val := val
| (some info) val := info.leading.toString ++ val ++ info.trailing.toString

partial def reprint : Syntax → Option String
| (atom info val)           := reprintLeaf info val
| (ident info rawVal _ _ _) := reprintLeaf info rawVal.toString
| (node kind args _)        :=
  if kind == choiceKind then
    if args.size == 0 then failure
    else do
      s ← reprint (args.get 0),
      args.mfoldlFrom (λ s stx, do s' ← reprint stx, guard (s == s'), pure s) s 1
  else args.mfoldl (λ r stx, do s ← reprint stx, pure $ r ++ s) ""
| missing := ""

open Lean.Format

protected partial def formatStx : Syntax → Format
| (atom info val) := format $ repr val
| (ident _ _ val pre scopes) :=
  let scopes := pre.map format ++ scopes.reverse.map format in
  let scopes := match scopes with [] := format "" | _ := bracket "{" (joinSep scopes ", ") "}" in
  format "`" ++ format val ++ scopes
| (node kind args scopes) :=
  let scopes := match scopes with [] := format "" | _ := bracket "{" (joinSep scopes.reverse ", ") "}" in
  if kind.name = `Lean.Parser.noKind then
    sbracket $ scopes ++ joinSep (args.toList.map formatStx) line
  else
    let shorterName := kind.name.replacePrefix `Lean.Parser Name.anonymous in
    paren $ joinSep ((format shorterName ++ scopes) :: args.toList.map formatStx) line
| missing := "<missing>"

instance : HasFormat Syntax := ⟨Syntax.formatStx⟩
instance : ToString Syntax := ⟨toString ∘ format⟩
end Syntax

end Parser
-- end Lean
