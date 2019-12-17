/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich, Leonardo de Moura
-/
prelude
import Init.Data.Array
import Init.Lean.Data.Name
import Init.Lean.Data.Format

namespace Lean
structure SourceInfo :=
/- Will be inferred after parsing by `Syntax.updateLeading`. During parsing,
   it is not at all clear what the preceding token was, especially with backtracking. -/
(leading  : Substring)
(pos      : String.Pos)
(trailing : Substring)

namespace SourceInfo

def updateTrailing (info : SourceInfo) (trailing : Substring) : SourceInfo :=
{ trailing := trailing, .. info }

def truncateTrailing (info : SourceInfo) : SourceInfo :=
{ trailing := { stopPos := info.trailing.startPos, .. info.trailing }, .. info }

/- Update `info₁.trailing.stopPos` to `info₂.trailing.stopPos` -/
def appendToTrailing (info₁ info₂ : SourceInfo) : SourceInfo :=
{ trailing := { stopPos := info₂.trailing.stopPos, .. info₁.trailing }, .. info₁ }

/- Update `info₁.leading.startPos` to `info₂.leading.startPos` -/
def appendToLeading (info₁ info₂ : SourceInfo) : SourceInfo :=
{ leading := { startPos := info₂.leading.startPos, .. info₁.leading }, .. info₁ }

end SourceInfo

/- Node kind generation -/

abbrev SyntaxNodeKind := Name

@[matchPattern] def choiceKind : SyntaxNodeKind := `choice
@[matchPattern] def nullKind : SyntaxNodeKind := `null
def strLitKind : SyntaxNodeKind := `strLit
def charLitKind : SyntaxNodeKind := `charLit
def numLitKind : SyntaxNodeKind := `numLit
def fieldIdxKind : SyntaxNodeKind := `fieldIdx

/- Syntax AST -/

inductive Syntax
| missing {} : Syntax
| node   (kind : SyntaxNodeKind) (args : Array Syntax) : Syntax
| atom   {} (info : Option SourceInfo) (val : String) : Syntax
| ident  {} (info : Option SourceInfo) (rawVal : Substring) (val : Name) (preresolved : List (Name × List String)) : Syntax

instance stxInh : Inhabited Syntax :=
⟨Syntax.missing⟩

def Syntax.isMissing : Syntax → Bool
| Syntax.missing => true
| _ => false

inductive IsNode : Syntax → Prop
| mk (kind : SyntaxNodeKind) (args : Array Syntax) : IsNode (Syntax.node kind args)

def SyntaxNode : Type := {s : Syntax // IsNode s }

def unreachIsNodeMissing {β} (h : IsNode Syntax.missing) : β := False.elim (nomatch h)
def unreachIsNodeAtom {β} {info val} (h : IsNode (Syntax.atom info val)) : β := False.elim (nomatch h)
def unreachIsNodeIdent {β info rawVal val preresolved} (h : IsNode (Syntax.ident info rawVal val preresolved)) : β := False.elim (nomatch h)

namespace SyntaxNode

@[inline] def getKind (n : SyntaxNode) : SyntaxNodeKind :=
match n with
| ⟨Syntax.node k args, _⟩   => k
| ⟨Syntax.missing, h⟩       => unreachIsNodeMissing h
| ⟨Syntax.atom _ _, h⟩      => unreachIsNodeAtom h
| ⟨Syntax.ident _ _ _ _, h⟩ => unreachIsNodeIdent h

@[inline] def withArgs {β} (n : SyntaxNode) (fn : Array Syntax → β) : β :=
match n with
| ⟨Syntax.node _ args, _⟩   => fn args
| ⟨Syntax.missing, h⟩       => unreachIsNodeMissing h
| ⟨Syntax.atom _ _, h⟩      => unreachIsNodeAtom h
| ⟨Syntax.ident _ _ _ _, h⟩ => unreachIsNodeIdent h

@[inline] def getNumArgs (n : SyntaxNode) : Nat :=
withArgs n $ fun args => args.size

@[inline] def getArg (n : SyntaxNode) (i : Nat) : Syntax :=
withArgs n $ fun args => args.get! i

@[inline] def getArgs (n : SyntaxNode) : Array Syntax :=
withArgs n $ fun args => args

@[inline] def modifyArgs (n : SyntaxNode) (fn : Array Syntax → Array Syntax) : Syntax :=
match n with
| ⟨Syntax.node kind args, _⟩ => Syntax.node kind (fn args)
| ⟨Syntax.missing, h⟩        => unreachIsNodeMissing h
| ⟨Syntax.atom _ _, h⟩       => unreachIsNodeAtom h
| ⟨Syntax.ident _ _ _ _,  h⟩ => unreachIsNodeIdent h

end SyntaxNode

namespace Syntax

def setAtomVal : Syntax → String → Syntax
| atom info _, v => (atom info v)
| stx,         _ => stx

@[inline] def ifNode {β} (stx : Syntax) (hyes : SyntaxNode → β) (hno : Unit → β) : β :=
match stx with
| Syntax.node k args => hyes ⟨Syntax.node k args, IsNode.mk k args⟩
| _                  => hno ()

@[inline] def ifNodeKind {β} (stx : Syntax) (kind : SyntaxNodeKind) (hyes : SyntaxNode → β) (hno : Unit → β) : β :=
match stx with
| Syntax.node k args => if k == kind then hyes ⟨Syntax.node k args, IsNode.mk k args⟩ else hno ()
| _                  => hno ()

def isAtom : Syntax → Bool
| atom _ _ => true
| _        => false

def isIdent : Syntax → Bool
| ident _ _ _ _ => true
| _             => false

def getId : Syntax → Name
| ident _ _ val _ => val
| _               => Name.anonymous

def isOfKind : Syntax → SyntaxNodeKind → Bool
| node kind _, k => k == kind
| _,           _ => false

def asNode : Syntax → SyntaxNode
| Syntax.node kind args => ⟨Syntax.node kind args, IsNode.mk kind args⟩
| _                     => ⟨Syntax.node nullKind #[], IsNode.mk nullKind #[]⟩

def getNumArgs (stx : Syntax) : Nat :=
stx.asNode.getNumArgs

def getArgs (stx : Syntax) : Array Syntax :=
stx.asNode.getArgs

def getArg (stx : Syntax) (i : Nat) : Syntax :=
stx.asNode.getArg i

def setArgs (stx : Syntax) (args : Array Syntax) : Syntax :=
match stx with
| node k _ => node k args
| stx      => stx

@[inline] def modifyArgs (stx : Syntax) (fn : Array Syntax → Array Syntax) : Syntax :=
match stx with
| node k args => node k (fn args)
| stx         => stx

def setArg (stx : Syntax) (i : Nat) (arg : Syntax) : Syntax :=
match stx with
| node k args => node k (args.set! i arg)
| stx         => stx

@[inline] def modifyArg (stx : Syntax) (i : Nat) (fn : Syntax → Syntax) : Syntax :=
match stx with
| node k args => node k (args.modify i fn)
| stx         => stx

def getIdAt (stx : Syntax) (i : Nat) : Name :=
(stx.getArg i).getId

def getKind (stx : Syntax) : SyntaxNodeKind :=
stx.asNode.getKind

@[specialize] partial def mreplace {m : Type → Type} [Monad m] (fn : Syntax → m (Option Syntax)) : Syntax → m (Syntax)
| stx@(node kind args) => do
  o ← fn stx;
  match o with
  | some stx => pure stx
  | none     => do args ← args.mapM mreplace; pure (node kind args)
| stx => do o ← fn stx; pure $ o.getD stx

@[specialize] partial def mrewriteBottomUp {m : Type → Type} [Monad m] (fn : Syntax → m (Syntax)) : Syntax → m (Syntax)
| node kind args   => do
  args ← args.mapM mrewriteBottomUp;
  fn (node kind args)
| stx => fn stx

@[inline] def rewriteBottomUp (fn : Syntax → Syntax) (stx : Syntax) : Syntax :=
Id.run $ stx.mrewriteBottomUp fn

private def updateInfo : SourceInfo → String.Pos → SourceInfo
| {leading := {str := s, startPos := _, stopPos := _}, pos := pos, trailing := trailing}, last =>
  {leading := {str := s, startPos := last, stopPos := pos}, pos := pos, trailing := trailing}

/- Remark: the State `String.Pos` is the `SourceInfo.trailing.stopPos` of the previous token,
   or the beginning of the String. -/
@[inline]
private def updateLeadingAux : Syntax → StateM String.Pos (Option Syntax)
| atom (some info) val   => do
  last ← get;
  set info.trailing.stopPos;
  let newInfo := updateInfo info last;
  pure $ some (atom (some newInfo) val)
| ident (some info) rawVal val pre   => do
  last ← get;
  set info.trailing.stopPos;
  let newInfo := updateInfo info last;
  pure $ some (ident (some newInfo) rawVal val pre)
| _ => pure none

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
fun stx => (mreplace updateLeadingAux stx).run' 0

partial def updateTrailing (trailing : Substring) : Syntax → Syntax
| Syntax.atom (some info) val               => Syntax.atom (some (info.updateTrailing trailing)) val
| Syntax.ident (some info) rawVal val pre   => Syntax.ident (some (info.updateTrailing trailing)) rawVal val pre
| n@(Syntax.node k args)                    =>
  if args.size == 0 then n
  else
   let i    := args.size - 1;
   let last := updateTrailing (args.get! i);
   let args := args.set! i last;
   Syntax.node k args
| s => s

/-- Retrieve the left-most leaf's info in the Syntax tree. -/
partial def getHeadInfo : Syntax → Option SourceInfo
| atom info _      => info
| ident info _ _ _ => info
| node _ args      => args.find? getHeadInfo
| _                => none

def getPos (stx : Syntax) : Option String.Pos :=
SourceInfo.pos <$> stx.getHeadInfo

partial def getTailInfo : Syntax → Option SourceInfo
| atom info _      => info
| ident info _ _ _ => info
| node _ args      => args.findRev? getTailInfo
| _                => none

@[specialize] private partial def updateLast {α} [Inhabited α] (a : Array α) (f : α → Option α) : Nat → Option (Array α)
| i =>
  if i == 0 then none
  else
    let i := i - 1;
    let v := a.get! i;
    match f v with
    | some v => some $ a.set! i v
    | none   => updateLast i

partial def setTailInfoAux (info : Option SourceInfo) : Syntax → Option Syntax
| atom _ val             => some $ atom info val
| ident _ rawVal val pre => some $ ident info rawVal val pre
| node k args            =>
  match updateLast args setTailInfoAux args.size with
  | some args => some $ node k args
  | none      => none
| stx                    => none

def setTailInfo (stx : Syntax) (info : Option SourceInfo) : Syntax :=
match setTailInfoAux info stx with
| some stx => stx
| none     => stx

private def reprintLeaf : Option SourceInfo → String → String
| none,      val => val
| some info, val => info.leading.toString ++ val ++ info.trailing.toString

partial def reprint : Syntax → Option String
| atom info val           => reprintLeaf info val
| ident info rawVal _ _   => reprintLeaf info rawVal.toString
| node kind args          =>
  if kind == choiceKind then
    if args.size == 0 then failure
    else do
      s ← reprint (args.get! 0);
      args.foldlFromM (fun s stx => do s' ← reprint stx; guard (s == s'); pure s) s 1
  else args.foldlM (fun r stx => do s ← reprint stx; pure $ r ++ s) ""
| _ => ""

open Lean.Format

protected partial def formatStx : Syntax → Format
| atom info val     => format $ repr val
| ident _ _ val pre => format "`" ++ format val
| node kind args    =>
  if kind == `Lean.Parser.noKind then
    sbracket $ joinSep (args.toList.map formatStx) line
  else
    let shorterName := kind.replacePrefix `Lean.Parser Name.anonymous;
    paren $ joinSep ((format shorterName) :: args.toList.map formatStx) line
| missing => "<missing>"

instance : HasFormat (Syntax)   := ⟨Syntax.formatStx⟩
instance : HasToString (Syntax) := ⟨toString ∘ format⟩

end Syntax

namespace SyntaxNode

@[inline] def getIdAt (n : SyntaxNode) (i : Nat) : Name :=
(n.getArg i).getId

end SyntaxNode

/- Helper functions for creating Syntax objects using C++ -/

@[export lean_mk_syntax_atom]
def mkSimpleAtomCore (val : String) : Syntax :=
Syntax.atom none val

@[export lean_mk_syntax_ident]
def mkSimpleIdent (val : Name) : Syntax :=
Syntax.ident none (toString val).toSubstring val []

@[export lean_mk_syntax_list]
def mkListNode (args : Array Syntax) : Syntax :=
Syntax.node nullKind args

def mkAtom (val : String) : Syntax :=
Syntax.atom none val

@[inline] def mkNode (k : SyntaxNodeKind) (args : Array Syntax) : Syntax :=
Syntax.node k args

@[inline] def mkNullNode (args : Array Syntax := #[]) : Syntax :=
Syntax.node nullKind args

def mkOptionalNode (arg : Option Syntax) : Syntax :=
match arg with
| some arg => Syntax.node nullKind #[arg]
| none     => Syntax.node nullKind #[]

/- Helper functions for creating string and numeric literals -/

def mkStxLit (kind : SyntaxNodeKind) (val : String) (info : Option SourceInfo := none) : Syntax :=
let atom : Syntax := Syntax.atom info val;
Syntax.node kind #[atom]

def mkStxStrLit (val : String) (info : Option SourceInfo := none) : Syntax :=
mkStxLit strLitKind val info

def mkStxNumLit (val : String) (info : Option SourceInfo := none) : Syntax :=
mkStxLit numLitKind val info

@[export lean_mk_syntax_str_lit]
def mkStxStrLitAux (val : String) : Syntax :=
mkStxStrLit val

@[export lean_mk_syntax_num_lit]
def mkStxNumLitAux (val : Nat) : Syntax :=
mkStxNumLit (toString val)

namespace Syntax

def isStrLit? : Syntax → Option String
| Syntax.node k args   =>
  if k == strLitKind && args.size == 1 then
    match args.get! 0 with
    | (Syntax.atom _ val) => some val
    | _ => none
  else
    none
| _ => none

/- Recall that we don't have special Syntax constructors for storing numeric atoms.
   The idea is to have an extensible approach where embedded DSLs may have new kind of atoms and/or
   different ways of representing them. So, our atoms contain just the parsed string.
   The main Lean parser uses the kind `numLitKind` for storing natural numbers that can be encoded
   in binary, octal, decimal and hexadecimal format. `isNatLit` implements a "decoder"
   for Syntax objects representing these numerals. -/

private partial def decodeBinLitAux (s : String) : Nat → Nat → Option Nat
| i, val =>
  if s.atEnd i then some val
  else
    let c := s.get i;
    if c == '0' then decodeBinLitAux (s.next i) (2*val)
    else if c == '1' then decodeBinLitAux (s.next i) (2*val + 1)
    else none

private partial def decodeOctalLitAux (s : String) : Nat → Nat → Option Nat
| i, val =>
  if s.atEnd i then some val
  else
    let c := s.get i;
    if '0' ≤ c && c ≤ '7' then decodeOctalLitAux (s.next i) (8*val + c.toNat - '0'.toNat)
    else none

private partial def decodeHexLitAux (s : String) : Nat → Nat → Option Nat
| i, val =>
  if s.atEnd i then some val
  else
    let c := s.get i;
    if '0' ≤ c && c ≤ '9' then decodeHexLitAux (s.next i) (16*val + c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then decodeHexLitAux (s.next i) (16*val + 10 + c.toNat - 'a'.toNat)
    else if 'A' ≤ c && c ≤ 'F' then decodeHexLitAux (s.next i) (16*val + 10 + c.toNat - 'A'.toNat)
    else none

private partial def decodeDecimalLitAux (s : String) : Nat → Nat → Option Nat
| i, val =>
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
| Syntax.node k args   =>
  if k == nodeKind && args.size == 1 then
    match args.get! 0 with
    | (Syntax.atom _ val) => decodeNatLitVal val
    | _ => none
  else
    none
| _ => none

def isNatLit? (s : Syntax) : Option Nat :=
isNatLitAux numLitKind s

def isFieldIdx? (s : Syntax) : Option Nat :=
isNatLitAux fieldIdxKind s

def isIdOrAtom? : Syntax → Option String
| Syntax.atom _ val           => some val
| Syntax.ident _ rawVal _ _   => some rawVal.toString
| _ => none

def toNat (stx : Syntax) : Nat :=
match stx.isNatLit? with
| some val => val
| none     => 0

end Syntax

/-- Create an identifier using `SourceInfo` from `src` -/
def mkIdentFrom (src : Syntax) (val : Name) : Syntax :=
let info := src.getHeadInfo;
Syntax.ident info (toString val).toSubstring val []

def mkAtomFrom (src : Syntax) (val : String) : Syntax :=
let info := src.getHeadInfo;
Syntax.atom info val

end Lean
