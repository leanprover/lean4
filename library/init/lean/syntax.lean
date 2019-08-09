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

inductive Syntax (α : Type := Empty)
| missing {} : Syntax
| node   (kind : SyntaxNodeKind) (args : Array Syntax) : Syntax
| atom   {} (info : Option SourceInfo) (val : String) : Syntax
| ident  {} (info : Option SourceInfo) (rawVal : Substring) (val : Name) (preresolved : List (Nat × Name)) : Syntax
| other  : α → Syntax

instance stxInh {α} : Inhabited (Syntax α) :=
⟨Syntax.missing⟩

def Syntax.isMissing {α} : Syntax α → Bool
| Syntax.missing := true
| _ := false

inductive IsNode {α} : Syntax α → Prop
| mk (kind : SyntaxNodeKind) (args : Array (Syntax α)) : IsNode (Syntax.node kind args)

def SyntaxNode (α : Type := Empty) : Type := {s : Syntax α // IsNode s }

def unreachIsNodeMissing {α β} (h : IsNode (@Syntax.missing α)) : β := False.elim (nomatch h)
def unreachIsNodeAtom {α β} {info val} (h : IsNode (@Syntax.atom α info val)) : β := False.elim (nomatch h)
def unreachIsNodeIdent {α β info rawVal val preresolved} (h : IsNode (@Syntax.ident α info rawVal val preresolved)) : β := False.elim (nomatch h)
def unreachIsNodeOther {α β} {a : α} (h : IsNode (Syntax.other a)) : β := False.elim (nomatch h)

namespace SyntaxNode

@[inline] def getKind {α} (n : SyntaxNode α) : SyntaxNodeKind :=
match n with
| ⟨Syntax.node k args, _⟩   => k
| ⟨Syntax.missing, h⟩       => unreachIsNodeMissing h
| ⟨Syntax.atom _ _, h⟩      => unreachIsNodeAtom h
| ⟨Syntax.ident _ _ _ _, h⟩ => unreachIsNodeIdent h
| ⟨Syntax.other _ , h⟩      => unreachIsNodeOther h

@[inline] def withArgs {α β} (n : SyntaxNode α) (fn : Array (Syntax α) → β) : β :=
match n with
| ⟨Syntax.node _ args, _⟩   => fn args
| ⟨Syntax.missing, h⟩       => unreachIsNodeMissing h
| ⟨Syntax.atom _ _, h⟩      => unreachIsNodeAtom h
| ⟨Syntax.ident _ _ _ _, h⟩ => unreachIsNodeIdent h
| ⟨Syntax.other _ , h⟩      => unreachIsNodeOther h

@[inline] def getNumArgs {α} (n : SyntaxNode α) : Nat :=
withArgs n $ fun args => args.size

@[inline] def getArg {α} (n : SyntaxNode α) (i : Nat) : Syntax α :=
withArgs n $ fun args => args.get i

@[inline] def getArgs {α} (n : SyntaxNode α) : Array (Syntax α) :=
withArgs n $ fun args => args

@[inline] def updateArgs {α} (n : SyntaxNode α) (fn : Array (Syntax α) → Array (Syntax α)) : Syntax α :=
match n with
| ⟨Syntax.node kind args, _⟩ => Syntax.node kind (fn args)
| ⟨Syntax.missing, h⟩        => unreachIsNodeMissing h
| ⟨Syntax.atom _ _, h⟩       => unreachIsNodeAtom h
| ⟨Syntax.ident _ _ _ _,  h⟩ => unreachIsNodeIdent h
| ⟨Syntax.other _, h⟩        => unreachIsNodeOther h

end SyntaxNode

namespace Syntax

def setAtomVal {α} : Syntax α → String → Syntax α
| (atom info _) v := (atom info v)
| stx           _ := stx

@[inline] def ifNode {α β} (stx : Syntax α) (hyes : SyntaxNode α → β) (hno : Unit → β) : β :=
match stx with
| Syntax.node k args => hyes ⟨Syntax.node k args, IsNode.mk k args⟩
| _                  => hno ()

@[inline] def ifNodeKind {α β} (stx : Syntax α) (kind : SyntaxNodeKind) (hyes : SyntaxNode α → β) (hno : Unit → β) : β :=
match stx with
| Syntax.node k args => if k == kind then hyes ⟨Syntax.node k args, IsNode.mk k args⟩ else hno ()
| _                  => hno ()

def isIdent {α} : Syntax α → Bool
| (ident _ _ _ _) := true
| _               := false

def getId {α} : Syntax α → Name
| (ident _ _ val _) := val
| _                 := Name.anonymous

def isOfKind {α} : Syntax α → SyntaxNodeKind → Bool
| (node kind _) k := k == kind
| _             _ := false

def asNode {α} : Syntax α → SyntaxNode α
| (Syntax.node kind args) := ⟨Syntax.node kind args, IsNode.mk kind args⟩
| _                       := ⟨Syntax.node nullKind Array.empty, IsNode.mk nullKind Array.empty⟩

def getNumArgs {α} (stx : Syntax α) : Nat :=
stx.asNode.getNumArgs

def getArgs {α} (stx : Syntax α) : Array (Syntax α) :=
stx.asNode.getArgs

def getArg {α} (stx : Syntax α) (i : Nat) : Syntax α :=
stx.asNode.getArg i

def getIdAt {α} (stx : Syntax α) (i : Nat) : Name :=
(stx.getArg i).getId

def getKind {α} (stx : Syntax α) : SyntaxNodeKind :=
stx.asNode.getKind

@[specialize] partial def mreplace {α} {m : Type → Type} [Monad m] (fn : Syntax α → m (Option (Syntax α))) : Syntax α → m (Syntax α)
| stx@(node kind args) := do
  o ← fn stx;
  match o with
  | some stx => pure stx
  | none     => do args ← args.mmap mreplace; pure (node kind args)
| stx := do o ← fn stx; pure (o.getOrElse stx)

@[specialize] partial def mrewriteBottomUp {α} {m : Type → Type} [Monad m] (fn : Syntax α → m (Syntax α)) : Syntax α → m (Syntax α)
| (node kind args) := do
  args ← args.mmap mrewriteBottomUp;
  fn (node kind args)
| stx := fn stx

@[inline] def rewriteBottomUp {α} (fn : Syntax α → Syntax α) (stx : Syntax α) : Syntax α :=
Id.run $ stx.mrewriteBottomUp fn

private def updateInfo : SourceInfo → String.Pos → SourceInfo
| {leading := {str := s, startPos := _, stopPos := _}, pos := pos, trailing := trailing} last :=
  {leading := {str := s, startPos := last, stopPos := pos}, pos := pos, trailing := trailing}

/- Remark: the State `String.Pos` is the `SourceInfo.trailing.stopPos` of the previous token,
   or the beginning of the String. -/
@[inline]
private def updateLeadingAux {α} : Syntax α → State String.Pos (Option (Syntax α))
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
def updateLeading {α} : Syntax α → Syntax α :=
fun stx => (mreplace updateLeadingAux stx).run' 0

partial def updateTrailing {α} (trailing : Substring) : Syntax α → Syntax α
| (Syntax.atom (some info) val)             := Syntax.atom (some (info.updateTrailing trailing)) val
| (Syntax.ident (some info) rawVal val pre) := Syntax.ident (some (info.updateTrailing trailing)) rawVal val pre
| n@(Syntax.node k args)                    :=
  if args.size == 0 then n
  else
   let i    := args.size - 1;
   let last := updateTrailing (args.get i);
   let args := args.set i last;
   Syntax.node k args
| s := s

/-- Retrieve the left-most leaf's info in the Syntax tree. -/
partial def getLeftMostInfo {α} : Syntax α → Option SourceInfo
| (atom info _)       := info
| (ident info _ _ _ ) := info
| (node _ args)       := args.find getLeftMostInfo
| _                   := none

def getPos {α} (stx : Syntax α) : Option String.Pos :=
SourceInfo.pos <$> stx.getLeftMostInfo

partial def getTailInfo {α} : Syntax α → Option SourceInfo
| (atom info _)       := info
| (ident info _ _ _)  := info
| (node _ args)       := getTailInfo args.back
| _                   := none

partial def setTailInfo {α} : Syntax α → Option SourceInfo → Syntax α
| (atom _ val)             info := atom info val
| (ident _ rawVal val pre) info := ident info rawVal val pre
| (node k args)            info := node k $ args.modify (args.size - 1) $ fun arg => setTailInfo arg info
| stx                      _    := stx

partial def getHeadInfo {α} : Syntax α → Option SourceInfo
| (atom info _)       := info
| (ident info _ _ _)  := info
| (node _ args)       := getHeadInfo $ args.get 0
| _                   := none

partial def setHeadInfo {α} : Syntax α → Option SourceInfo → Syntax α
| (atom _ val)             info := atom info val
| (ident _ rawVal val pre) info := ident info rawVal val pre
| (node k args)            info := node k $ args.modify 0 $ fun arg => setTailInfo arg info
| stx                      _    := stx

private def reprintLeaf : Option SourceInfo → String → String
| none        val := val
| (some info) val := info.leading.toString ++ val ++ info.trailing.toString

partial def reprint {α} : Syntax α → Option String
| (atom info val)         := reprintLeaf info val
| (ident info rawVal _ _) := reprintLeaf info rawVal.toString
| (node kind args)        :=
  if kind == choiceKind then
    if args.size == 0 then failure
    else do
      s ← reprint (args.get 0);
      args.mfoldlFrom (fun s stx => do s' ← reprint stx; guard (s == s'); pure s) s 1
  else args.mfoldl (fun r stx => do s ← reprint stx; pure $ r ++ s) ""
| _ := ""

open Lean.Format

protected partial def formatStx {α} : Syntax α → Format
| (atom info val)     := format $ repr val
| (ident _ _ val pre) := format "`" ++ format val
| (node kind args)    :=
  if kind = `Lean.Parser.noKind then
    sbracket $ joinSep (args.toList.map formatStx) line
  else
    let shorterName := kind.replacePrefix `Lean.Parser Name.anonymous;
    paren $ joinSep ((format shorterName) :: args.toList.map formatStx) line
| missing   := "<missing>"
| (other _) := "<other>"

instance {α} : HasFormat (Syntax α)   := ⟨Syntax.formatStx⟩
instance {α} : HasToString (Syntax α) := ⟨toString ∘ format⟩

end Syntax

namespace SyntaxNode

@[inline] def getIdAt {α} (n : SyntaxNode α) (i : Nat) : Name :=
(n.getArg i).getId

end SyntaxNode

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
let atom : Syntax := Syntax.atom info val;
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

def isStrLit {α} : Syntax α → Option String
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

def isNatLitAux {α} (nodeKind : SyntaxNodeKind) : Syntax α → Option Nat
| (Syntax.node k args) :=
  if k == nodeKind && args.size == 1 then
    match args.get 0 with
    | (Syntax.atom _ val) => decodeNatLitVal val
    | _ => none
  else
    none
| _ := none

def isNatLit {α} (s : Syntax α) : Option Nat :=
isNatLitAux numLitKind s

def isFieldIdx {α} (s : Syntax α) : Option Nat :=
isNatLitAux fieldIdxKind s

def isIdOrAtom {α} : Syntax α → Option String
| (Syntax.atom _ val)         := some val
| (Syntax.ident _ rawVal _ _) := some rawVal.toString
| _ := none

end Syntax

end Lean
