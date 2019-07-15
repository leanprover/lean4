/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich, Leonardo de Moura
-/
prelude
import init.lean.name init.lean.format init.data.array

namespace Lean
structure SourceInfo :=
/- Will be inferred after parsing by `Syntax.updateLeading`. During parsing,
   it is not at all clear what the preceding token was, especially with backtracking. -/
(leading  : Substring)
(pos      : String.Pos)
(trailing : Substring)

def SourceInfo.updateTrailing : SourceInfo → Substring → SourceInfo
| ⟨leading, pos, _⟩ trailing := ⟨leading, pos, trailing⟩

/- Node kind generation -/

abbrev SyntaxNodeKind := Name

@[matchPattern] def choiceKind : SyntaxNodeKind := `choice
@[matchPattern] def nullKind : SyntaxNodeKind := `null
def strLitKind : SyntaxNodeKind := `strLit
def numLitKind : SyntaxNodeKind := `numLit
def fieldIdxKind : SyntaxNodeKind := `fieldIdx

/- Syntax AST -/

inductive Syntax
| missing
| node   (kind : SyntaxNodeKind) (args : Array Syntax)
| atom   (info : Option SourceInfo) (val : String)
| ident  (info : Option SourceInfo) (rawVal : Substring) (val : Name) (preresolved : List Name)

instance stxInh : Inhabited Syntax :=
⟨Syntax.missing⟩

def Syntax.isMissing : Syntax → Bool
| Syntax.missing := true
| _ := false

inductive IsNode : Syntax → Prop
| mk (kind : SyntaxNodeKind) (args : Array Syntax) : IsNode (Syntax.node kind args)

def SyntaxNode : Type := {s : Syntax // IsNode s }

def notIsNodeMissing (h : IsNode Syntax.missing) : False                   := match h with end
def notIsNodeAtom   {info val} (h : IsNode (Syntax.atom info val)) : False := match h with end
def notIsNodeIdent  {info rawVal val preresolved} (h : IsNode (Syntax.ident info rawVal val preresolved)) : False := match h with end

def unreachIsNodeMissing {α : Type} (h : IsNode Syntax.missing) : α := False.elim (notIsNodeMissing h)
def unreachIsNodeAtom {α : Type} {info val} (h : IsNode (Syntax.atom info val)) : α := False.elim (notIsNodeAtom h)
def unreachIsNodeIdent {α : Type} {info rawVal val preresolved} (h : IsNode (Syntax.ident info rawVal val preresolved)) : α :=
False.elim (match h with end)

@[inline] def withArgs {α : Type} (n : SyntaxNode) (fn : Array Syntax → α) : α :=
match n with
| ⟨Syntax.node _ args, _⟩ => fn args
| ⟨Syntax.missing, h⟩       => unreachIsNodeMissing h
| ⟨Syntax.atom _ _, h⟩      => unreachIsNodeAtom h
| ⟨Syntax.ident _ _ _ _, h⟩ => unreachIsNodeIdent h

@[inline] def updateArgs (n : SyntaxNode) (fn : Array Syntax → Array Syntax) : Syntax :=
match n with
| ⟨Syntax.node kind args, _⟩ => Syntax.node kind (fn args)
| ⟨Syntax.missing, h⟩        => unreachIsNodeMissing h
| ⟨Syntax.atom _ _, h⟩       => unreachIsNodeAtom h
| ⟨Syntax.ident _ _ _ _,  h⟩ => unreachIsNodeIdent h

namespace Syntax
def isIdent : Syntax → Bool
| (Syntax.ident _ _ _ _) := true
| _                      := false

def isOfKind : Syntax → SyntaxNodeKind → Bool
| (Syntax.node kind _) k := k == kind
| other                _ := false

@[specialize] partial def mreplace {m : Type → Type} [Monad m] (fn : Syntax → m (Option Syntax)) : Syntax → m Syntax
| stx@(node kind args) := do
  o ← fn stx;
  match o with
  | some stx => pure stx
  | none     => do args ← args.mmap mreplace; pure (node kind args)
| stx := do o ← fn stx; pure (o.getOrElse stx)

@[inline] def replace {m : Type → Type} [Monad m] (fn : Syntax → m (Option Syntax)) := @mreplace Id _

private def updateInfo : SourceInfo → String.Pos → SourceInfo
| {leading := {str := s, startPos := _, stopPos := _}, pos := pos, trailing := trailing} last :=
  {leading := {str := s, startPos := last, stopPos := pos}, pos := pos, trailing := trailing}

/- Remark: the State `String.Pos` is the `SourceInfo.trailing.stopPos` of the previous token,
   or the beginning of the String. -/
@[inline]
private def updateLeadingAux : Syntax → State String.Pos (Option Syntax)
| (atom (some info) val) := do
  last ← get;
  set info.trailing.stopPos;
  let newInfo := updateInfo info last;
  pure $ some (atom (some newInfo) val)
| (ident (some info) rawVal val pre) := do
  last ← get;
  set info.trailing.stopPos;
  let newInfo := updateInfo info last;
  pure $ some (ident (some newInfo) rawVal val pre)
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
fun stx => Prod.fst <$> (mreplace updateLeadingAux stx).run 0

partial def updateTrailing (trailing : Substring) : Syntax → Syntax
| (Syntax.atom (some info) val)             := Syntax.atom (some (info.updateTrailing trailing)) val
| (Syntax.ident (some info) rawVal val pre) := Syntax.ident (some (info.updateTrailing trailing)) rawVal val pre
| n@(Syntax.node k args)                    :=
  if args.size == 0 then n
  else
   let i    := args.size - 1;
   let last := updateTrailing (args.get i);
   let args := args.set i last;
   Syntax.node k args
| other := other

/-- Retrieve the left-most leaf's info in the Syntax tree. -/
partial def getHeadInfo : Syntax → Option SourceInfo
| missing             := none
| (atom info _)       := info
| (ident info _ _ _ ) := info
| (node _ args)       := args.find getHeadInfo

def getPos (stx : Syntax) : Option String.Pos :=
SourceInfo.pos <$> stx.getHeadInfo

partial def getTailInfo : Syntax → Option SourceInfo
| missing             := none
| (atom info _)       := info
| (ident info _ _ _)  := info
| (node _ args)       := args.findRev getTailInfo

private def reprintLeaf : Option SourceInfo → String → String
| none        val := val
| (some info) val := info.leading.toString ++ val ++ info.trailing.toString

partial def reprint : Syntax → Option String
| (atom info val)         := reprintLeaf info val
| (ident info rawVal _ _) := reprintLeaf info rawVal.toString
| (node kind args)        :=
  if kind == choiceKind then
    if args.size == 0 then failure
    else do
      s ← reprint (args.get 0);
      args.mfoldlFrom (fun s stx => do s' ← reprint stx; guard (s == s'); pure s) s 1
  else args.mfoldl (fun r stx => do s ← reprint stx; pure $ r ++ s) ""
| missing := ""

open Lean.Format

protected partial def formatStx : Syntax → Format
| (atom info val)     := format $ repr val
| (ident _ _ val pre) := format "`" ++ format val
| (node kind args)    :=
  if kind = `Lean.Parser.noKind then
    sbracket $ joinSep (args.toList.map formatStx) line
  else
    let shorterName := kind.replacePrefix `Lean.Parser Name.anonymous;
    paren $ joinSep ((format shorterName) :: args.toList.map formatStx) line
| missing := "<missing>"

instance : HasFormat Syntax := ⟨Syntax.formatStx⟩
instance : HasToString Syntax := ⟨toString ∘ format⟩

end Syntax

/- Helper functions for creating Syntax objects using C++ -/

@[export lean.mk_syntax_atom_core]
def mkSimpleAtom (val : String) : Syntax :=
Syntax.atom none val

@[export lean.mk_syntax_ident_core]
def mkSimpleIdent (val : Name) : Syntax :=
Syntax.ident none (toString val).toSubstring val []

@[export lean.mk_syntax_list_core]
def mkListNode (args : Array Syntax) : Syntax :=
Syntax.node nullKind args

/- Helper functions for creating string and numeric literals -/

def mkLit (kind : SyntaxNodeKind) (val : String) (info : Option SourceInfo := none) : Syntax :=
let atom := Syntax.atom info val;
Syntax.node kind (Array.singleton atom)

def mkStrLit (val : String) (info : Option SourceInfo := none) : Syntax :=
mkLit strLitKind val info

def mkNumLit (val : String) (info : Option SourceInfo := none) : Syntax :=
mkLit numLitKind val info

@[export lean.mk_syntax_str_lit_core]
def mkStrLitAux (val : String) : Syntax :=
mkStrLit val

@[export lean.mk_syntax_num_lit_core]
def mkNumLitAux (val : Nat) : Syntax :=
mkNumLit (toString val)

namespace Syntax

def isStrLit : Syntax → Option String
| (Syntax.node k args) :=
  if k == strLitKind && args.size == 1 then
    match args.get 0 with
    | (Syntax.atom _ val) => some val
    | _ => none
  else
    none
| _ := none

/- Recall that we don't have special Syntax constructors for storing numeric atoms.
   The idea is to have an extensible approach where embedded DSLs may have new kind of atoms and/or
   different ways of representing them. So, our atoms contain just the parsed string.
   The main Lean parser uses the kind `numLitKind` for storing natural numbers that can be encoded
   in binary, octal, decimal and hexadecimal format. `isNatLit` implements a "decoder"
   for Syntax objects representing these numerals. -/

private partial def decodeBinLitAux (s : String) : Nat → Nat → Option Nat
| i val :=
  if s.atEnd i then some val
  else
    let c := s.get i;
    if c == '0' then decodeBinLitAux (s.next i) (2*val)
    else if c == '1' then decodeBinLitAux (s.next i) (2*val + 1)
    else none

private partial def decodeOctalLitAux (s : String) : Nat → Nat → Option Nat
| i val :=
  if s.atEnd i then some val
  else
    let c := s.get i;
    if '0' ≤ c && c ≤ '7' then decodeOctalLitAux (s.next i) (8*val + c.toNat - '0'.toNat)
    else none

private partial def decodeHexLitAux (s : String) : Nat → Nat → Option Nat
| i val :=
  if s.atEnd i then some val
  else
    let c := s.get i;
    if '0' ≤ c && c ≤ '9' then decodeHexLitAux (s.next i) (16*val + c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then decodeHexLitAux (s.next i) (16*val + 10 + c.toNat - 'a'.toNat)
    else if 'A' ≤ c && c ≤ 'F' then decodeHexLitAux (s.next i) (16*val + 10 + c.toNat - 'A'.toNat)
    else none

private partial def decodeDecimalLitAux (s : String) : Nat → Nat → Option Nat
| i val :=
  if s.atEnd i then some val
  else
    let c := s.get i;
    if '0' ≤ c && c ≤ '9' then decodeDecimalLitAux (s.next i) (10*val + c.toNat - '0'.toNat)
    else none

private def decodeNatLitVal (s : String) : Option Nat :=
let len := s.length;
if len == 0 then none
else
  let c := s.get 0;
  if c == '0' then
    if len == 1 then some 0
    else
      let c := s.get 1;
      if c == 'x' || c == 'X' then decodeHexLitAux s 2 0
      else if c == 'b' || c == 'B' then decodeBinLitAux s 2 0
      else if c == 'o' || c == 'O' then decodeOctalLitAux s 2 0
      else if c.isDigit then decodeDecimalLitAux s 0 0
      else none
  else if c.isDigit then decodeDecimalLitAux s 0 0
  else none

def isNatLitAux (nodeKind : SyntaxNodeKind) : Syntax → Option Nat
| (Syntax.node k args) :=
  if k == nodeKind && args.size == 1 then
    match args.get 0 with
    | (Syntax.atom _ val) => decodeNatLitVal val
    | _ => none
  else
    none
| _ := none

def isNatLit (s : Syntax) : Option Nat :=
isNatLitAux numLitKind s

def isFieldIdx (s : Syntax) : Option Nat :=
isNatLitAux fieldIdxKind s

def isIdOrAtom : Syntax → Option String
| (Syntax.atom _ val)         := some val
| (Syntax.ident _ rawVal _ _) := some rawVal.toString
| _ := none

end Syntax

end Lean
