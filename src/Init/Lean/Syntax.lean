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

/- Syntax AST -/

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

def asNode : Syntax → SyntaxNode
| Syntax.node kind args => ⟨Syntax.node kind args, IsNode.mk kind args⟩
| _                     => ⟨Syntax.node nullKind #[], IsNode.mk nullKind #[]⟩

def getNumArgs (stx : Syntax) : Nat :=
stx.asNode.getNumArgs

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

def getPos (stx : Syntax) : Option String.Pos :=
SourceInfo.pos <$> stx.getHeadInfo

partial def getTailWithInfo : Syntax → Option Syntax
| stx@(atom (some _) _)      => some stx
| stx@(ident (some _) _ _ _) => some stx
| node _ args                => args.findSomeRev? getTailWithInfo
| _                          => none

partial def getTailInfo : Syntax → Option SourceInfo
| atom info _      => info
| ident info _ _ _ => info
| node _ args      => args.findSomeRev? getTailInfo
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

def truncateTrailing (stx : Syntax) : Syntax :=
match stx.getTailInfo with
| none      => stx
| some info => stx.setTailInfo info.truncateTrailing

@[specialize] private partial def updateFirst {α} [Inhabited α] (a : Array α) (f : α → Option α) : Nat → Option (Array α)
| i =>
  if h : i < a.size then
    let v := a.get ⟨i, h⟩;
    match f v with
    | some v => some $ a.set ⟨i, h⟩ v
    | none   => updateFirst (i+1)
  else
    none

partial def setHeadInfoAux (info : Option SourceInfo) : Syntax → Option Syntax
| atom _ val             => some $ atom info val
| ident _ rawVal val pre => some $ ident info rawVal val pre
| node k args            =>
  match updateFirst args setHeadInfoAux args.size with
  | some args => some $ node k args
  | noxne      => none
| stx                    => none

def setHeadInfo (stx : Syntax) (info : Option SourceInfo) : Syntax :=
match setHeadInfoAux info stx with
| some stx => stx
| none     => stx

partial def replaceInfo (info : SourceInfo) : Syntax → Syntax
| atom _ val             => atom info val
| ident _ rawVal val pre => ident info rawVal val pre
| node k args            => node k $ args.map replaceInfo
| stx                    => stx

private def reprintLeaf : Option SourceInfo → String → String
-- no source info => add gracious amounts of whitespace to definitely separate tokens
-- Note that the proper pretty printer does not use this function.
-- The parser as well always produces source info, so round-tripping is still
-- guaranteed.
| none,      val => " " ++ val ++ " "
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

partial def formatStxAux (maxDepth : Option Nat) : Nat → Syntax → Format
| _,     atom info val     => format $ repr val
| _,     ident _ _ val pre => format "`" ++ format val
| _,     missing           => "<missing>"
| depth, node kind args    =>
  let depth := depth + 1;
  if kind == `Lean.Parser.noKind then
    sbracket $
      if depth > maxDepth.getD depth then
        ".."
      else
        joinSep (args.toList.map (formatStxAux depth)) line
  else
    let shorterName := kind.replacePrefix `Lean.Parser Name.anonymous;
    let header      := format shorterName;
    let body : List Format :=
      if depth > maxDepth.getD depth then [".."] else args.toList.map (formatStxAux depth);
    paren $ joinSep (header :: body) line

def formatStx (stx : Syntax) (maxDepth : Option Nat := none) : Format :=
formatStxAux maxDepth 0 stx

instance : HasFormat (Syntax)   := ⟨formatStx⟩
instance : HasToString (Syntax) := ⟨toString ∘ format⟩

end Syntax

namespace SyntaxNode

@[inline] def getIdAt (n : SyntaxNode) (i : Nat) : Name :=
(n.getArg i).getId

end SyntaxNode

/- Helper functions for creating Syntax objects using C++ -/

@[export lean_mk_syntax_atom]
def mkSimpleAtom (val : String) : Syntax :=
Syntax.atom none val

@[export lean_mk_syntax_list]
def mkListNode (args : Array Syntax) : Syntax :=
Syntax.node nullKind args

def mkAtom (val : String) : Syntax :=
Syntax.atom none val

@[inline] def mkNode (k : SyntaxNodeKind) (args : Array Syntax) : Syntax :=
Syntax.node k args

@[export lean_mk_syntax_str_lit]
def mkStxStrLitAux (val : String) : Syntax :=
mkStxStrLit val

@[export lean_mk_syntax_num_lit]
def mkStxNumLitAux (val : Nat) : Syntax :=
mkStxNumLit (toString val)


/-- Reflect a runtime datum back to surface syntax (best-effort). -/
class HasQuote (α : Type) :=
(quote : α → Syntax)

export HasQuote (quote)

instance Syntax.HasQuote : HasQuote Syntax := ⟨id⟩
instance String.HasQuote : HasQuote String := ⟨fun s => Syntax.node `Lean.Parser.Term.str #[mkStxStrLit s]⟩
instance Nat.HasQuote : HasQuote Nat := ⟨fun n => Syntax.node `Lean.Parser.Term.num #[mkStxNumLit $ toString n]⟩
instance Substring.HasQuote : HasQuote Substring := ⟨fun s => mkCAppStx `String.toSubstring #[quote s.toString]⟩

private def quoteName : Name → Syntax
| Name.anonymous => mkCTermId `Lean.Name.anonymous
| Name.str n s _ => mkCAppStx `Lean.mkNameStr #[quoteName n, quote s]
| Name.num n i _ => mkCAppStx `Lean.mkNameNum #[quoteName n, quote i]

instance Name.hasQuote : HasQuote Name := ⟨quoteName⟩

instance Prod.hasQuote {α β : Type} [HasQuote α] [HasQuote β] : HasQuote (α × β) :=
⟨fun ⟨a, b⟩ => mkCAppStx `Prod.mk #[quote a, quote b]⟩

private def quoteList {α : Type} [HasQuote α] : List α → Syntax
| []      => mkCTermId `List.nil
| (x::xs) => mkCAppStx `List.cons #[quote x, quoteList xs]

instance List.hasQuote {α : Type} [HasQuote α] : HasQuote (List α) := ⟨quoteList⟩

instance Array.hasQuote {α : Type} [HasQuote α] : HasQuote (Array α) :=
⟨fun xs => mkCAppStx `List.toArray #[quote xs.toList]⟩

private def quoteOption {α : Type} [HasQuote α] : Option α → Syntax
| none     => mkTermId `Option.none
| (some x) => mkCAppStx `Option.some #[quote x]

instance Option.hasQuote {α : Type} [HasQuote α] : HasQuote (Option α) := ⟨quoteOption⟩

end Lean
