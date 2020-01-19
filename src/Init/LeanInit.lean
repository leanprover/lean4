/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura and Sebastian Ullrich
-/
prelude
import Init.Data.String.Basic
import Init.Data.Array.Basic
import Init.Data.UInt
import Init.Data.Hashable
import Init.Control.Reader
import Init.Control.Option

namespace Lean
/-
Basic Lean types used to implement builtin commands and extensions.
Note that this file is part of the Lean `Init` library instead of
`Lean` actual implementation.
The idea is to allow users to implement simple parsers, macros and tactics
without importing the whole `Lean` module.
It also allow us to use extensions to develop the `Init` library.
-/

/- Hierarchical names -/
inductive Name
| anonymous : Name
| str : Name → String → USize → Name
| num : Name → Nat → USize → Name

instance Name.inhabited : Inhabited Name :=
⟨Name.anonymous⟩

protected def Name.hash : Name → USize
| Name.anonymous => 1723
| Name.str p s h => h
| Name.num p v h => h

instance Name.hashable : Hashable Name := ⟨Name.hash⟩

@[export lean_name_mk_string]
def mkNameStr (p : Name) (s : String) : Name :=
Name.str p s $ mixHash (hash p) (hash s)

@[export lean_name_mk_numeral]
def mkNameNum (p : Name) (v : Nat) : Name :=
Name.num p v $ mixHash (hash p) (hash v)

def mkNameSimple (s : String) : Name :=
mkNameStr Name.anonymous s

namespace Name

@[extern "lean_name_eq"]
protected def Name.beq : (@& Name) → (@& Name) → Bool
| anonymous,   anonymous   => true
| str p₁ s₁ _, str p₂ s₂ _ => s₁ == s₂ && Name.beq p₁ p₂
| num p₁ n₁ _, num p₂ n₂ _ => n₁ == n₂ && Name.beq p₁ p₂
| _,           _           => false

instance : HasBeq Name := ⟨Name.beq⟩

def toStringWithSep (sep : String) : Name → String
| anonymous         => "[anonymous]"
| str anonymous s _ => s
| num anonymous v _ => toString v
| str n s _         => toStringWithSep n ++ sep ++ s
| num n v _         => toStringWithSep n ++ sep ++ repr v

protected def toString : Name → String :=
toStringWithSep "."

instance : HasToString Name :=
⟨Name.toString⟩

protected def append : Name → Name → Name
| n, anonymous => n
| n, str p s _ => mkNameStr (append n p) s
| n, num p d _ => mkNameNum (append n p) d

instance : HasAppend Name :=
⟨Name.append⟩

end Name

inductive ParserKind
| leading | trailing

/-
  Small DSL for describing parsers. We implement an interpreter for it
  at `Parser.lean` -/
inductive ParserDescrCore : ParserKind → Type
| andthen {k : ParserKind}       : ParserDescrCore k → ParserDescrCore k → ParserDescrCore k
| orelse  {k : ParserKind}       : ParserDescrCore k → ParserDescrCore k → ParserDescrCore k
| optional {k : ParserKind}      : ParserDescrCore k → ParserDescrCore k
| lookahead {k : ParserKind}     : ParserDescrCore k → ParserDescrCore k
| try {k : ParserKind}           : ParserDescrCore k → ParserDescrCore k
| many {k : ParserKind}          : ParserDescrCore k → ParserDescrCore k
| many1 {k : ParserKind}         : ParserDescrCore k → ParserDescrCore k
| sepBy {k : ParserKind}         : ParserDescrCore k → ParserDescrCore k → ParserDescrCore k
| sepBy1 {k : ParserKind}        : ParserDescrCore k → ParserDescrCore k → ParserDescrCore k
| node {k : ParserKind}          : Name → ParserDescrCore k → ParserDescrCore k
| symbol {k : ParserKind}        : String → Option Nat → ParserDescrCore k
| nonReservedSymbol              : String → Bool → ParserDescrCore ParserKind.leading
| num {k : ParserKind}           : ParserDescrCore k
| str {k : ParserKind}           : ParserDescrCore k
| char {k : ParserKind}          : ParserDescrCore k
| ident {k : ParserKind}         : ParserDescrCore k
| pushLeading                    : ParserDescrCore ParserKind.trailing
| parser {k : ParserKind}        : Name → Nat → ParserDescrCore k

instance ParserDescrCore.inhabited {k} : Inhabited (ParserDescrCore k) := ⟨ParserDescrCore.symbol "" none⟩

abbrev ParserDescr := ParserDescrCore ParserKind.leading
abbrev TrailingParserDescr := ParserDescrCore ParserKind.trailing

@[matchPattern] abbrev ParserDescr.andthen := @ParserDescrCore.andthen
@[matchPattern] abbrev ParserDescr.orelse := @ParserDescrCore.orelse
@[matchPattern] abbrev ParserDescr.optional := @ParserDescrCore.optional
@[matchPattern] abbrev ParserDescr.lookahead := @ParserDescrCore.lookahead
@[matchPattern] abbrev ParserDescr.try := @ParserDescrCore.try
@[matchPattern] abbrev ParserDescr.many := @ParserDescrCore.many
@[matchPattern] abbrev ParserDescr.many1 := @ParserDescrCore.many1
@[matchPattern] abbrev ParserDescr.sepBy := @ParserDescrCore.sepBy
@[matchPattern] abbrev ParserDescr.sepBy1 := @ParserDescrCore.sepBy1
@[matchPattern] abbrev ParserDescr.node := @ParserDescrCore.node
@[matchPattern] abbrev ParserDescr.symbol := @ParserDescrCore.symbol
@[matchPattern] abbrev ParserDescr.num := @ParserDescrCore.num
@[matchPattern] abbrev ParserDescr.str := @ParserDescrCore.str
@[matchPattern] abbrev ParserDescr.char := @ParserDescrCore.char
@[matchPattern] abbrev ParserDescr.ident := @ParserDescrCore.ident
@[matchPattern] abbrev ParserDescr.nonReservedSymbol := @ParserDescrCore.nonReservedSymbol
@[matchPattern] abbrev ParserDescr.pushLeading := @ParserDescrCore.pushLeading
@[matchPattern] abbrev ParserDescr.parser := @ParserDescrCore.parser

/- Syntax -/

structure SourceInfo :=
/- Will be inferred after parsing by `Syntax.updateLeading`. During parsing,
   it is not at all clear what the preceding token was, especially with backtracking. -/
(leading  : Substring)
(pos      : String.Pos)
(trailing : Substring)

abbrev SyntaxNodeKind := Name

/- Syntax AST -/

inductive Syntax
| missing {} : Syntax
| node   (kind : SyntaxNodeKind) (args : Array Syntax) : Syntax
| atom   {} (info : Option SourceInfo) (val : String) : Syntax
| ident  {} (info : Option SourceInfo) (rawVal : Substring) (val : Name) (preresolved : List (Name × List String)) : Syntax

instance Syntax.inhabited : Inhabited Syntax :=
⟨Syntax.missing⟩

namespace Syntax

def getKind (stx : Syntax) : SyntaxNodeKind :=
match stx with
| Syntax.node k args   => k
-- We use these "pseudo kinds" for antiquotation kinds.
-- For example, an antiquotation `$id:ident` (using Lean.Parser.Term.ident)
-- is compiled to ``if stx.isOfKind `ident ...``
| Syntax.missing       => `missing
| Syntax.atom _ v      => mkNameSimple v
| Syntax.ident _ _ _ _ => `ident

def isOfKind : Syntax → SyntaxNodeKind → Bool
| stx, k => stx.getKind == k

def getArg (stx : Syntax) (i : Nat) : Syntax :=
match stx with
| Syntax.node _ args => args.get! i
| _                  => arbitrary _

def getArgs (stx : Syntax) : Array Syntax :=
match stx with
| Syntax.node _ args => args
| _                  => #[]

/-- Retrieve the left-most leaf's info in the Syntax tree. -/
partial def getHeadInfo : Syntax → Option SourceInfo
| atom info _      => info
| ident info _ _ _ => info
| node _ args      => args.find? getHeadInfo
| _                => none

end Syntax

/-
Runtime support for making quotation terms auto-hygienic, by mangling identifiers
introduced by them with a "macro scope" supplied by the context. Details to appear in a
paper soon.
-/

abbrev MacroScope := Nat

/-- A monad that supports syntax quotations. Syntax quotations (in term
    position) are monadic values that when executed retrieve the current "macro
    scope" from the monad and apply it to every identifier they introduce
    (independent of whether this identifier turns out to be a reference to an
    existing declaration, or an actually fresh binding during further
    elaboration). -/
class MonadQuotation (m : Type → Type) :=
-- Get the fresh scope of the current macro invocation
(getCurrMacroScope {} : m MacroScope)
/- Execute action in a new macro invocation context. This transformer should be
   used at all places that morally qualify as the beginning of a "macro call",
   e.g. `elabCommand` and `elabTerm` in the case of the elaborator. However, it
   can also be used internally inside a "macro" if identifiers introduced by
   e.g. different recursive calls should be independent and not collide. While
   returning an intermediate syntax tree that will recursively be expanded by
   the elaborator can be used for the same effect, doing direct recursion inside
   the macro guarded by this transformer is often easier because one is not
   restricted to passing a single syntax tree. Modelling this helper as a
   transformer and not just a monadic action ensures that the current macro
   scope before the recursive call is restored after it, as expected. -/
(withFreshMacroScope {α : Type} : m α → m α)
export MonadQuotation

-- TODO: try harder to avoid clashes with other autogenerated names
def addMacroScope (n : Name) (scp : MacroScope) : Name :=
mkNameNum n scp

def addMacroScopes (n : Name) (scps : List MacroScope) : Name :=
scps.foldl addMacroScope n

abbrev MacroM := ReaderT MacroScope (OptionT Id)

instance MacroM.monadQuotation : MonadQuotation MacroM :=
{ getCurrMacroScope   := fun scp => some scp,
  withFreshMacroScope := fun _ x => x }

abbrev Macro := Syntax → MacroM Syntax

/- Builtin kinds -/

@[matchPattern] def choiceKind : SyntaxNodeKind := `choice
@[matchPattern] def nullKind : SyntaxNodeKind := `null
def strLitKind : SyntaxNodeKind := `strLit
def charLitKind : SyntaxNodeKind := `charLit
def numLitKind : SyntaxNodeKind := `numLit
def fieldIdxKind : SyntaxNodeKind := `fieldIdx

/- Helper functions for processing Syntax programmatically -/

/--
  Create an identifier using `SourceInfo` from `src`.
  To refer to a specific constant, use `mkCIdentFrom` instead. -/
def mkIdentFrom (src : Syntax) (val : Name) : Syntax :=
let info := src.getHeadInfo;
Syntax.ident info (toString val).toSubstring val []

/--
  Create an identifier referring to a constant `c` using `SourceInfo` from `src`.
  This variant of `mkIdentFrom` makes sure that the identifier cannot accidentally
  be captured. -/
def mkCIdentFrom (src : Syntax) (c : Name) : Syntax :=
let info := src.getHeadInfo;
Syntax.ident info (toString c).toSubstring (`_root_ ++ c) [(c, [])]

def mkAtomFrom (src : Syntax) (val : String) : Syntax :=
let info := src.getHeadInfo;
Syntax.atom info val

@[export lean_mk_syntax_ident]
def mkIdent (val : Name) : Syntax :=
Syntax.ident none (toString val).toSubstring val []

@[inline] def mkNullNode (args : Array Syntax := #[]) : Syntax :=
Syntax.node nullKind args

def mkOptionalNode (arg : Option Syntax) : Syntax :=
match arg with
| some arg => Syntax.node nullKind #[arg]
| none     => Syntax.node nullKind #[]

/-- Create syntax representing a Lean term application -/
def mkAppStx (fn : Syntax) (args : Array Syntax) : Syntax :=
Syntax.node `Lean.Parser.Term.app #[fn, mkNullNode args]

def mkHole (ref : Syntax) : Syntax :=
Syntax.node `Lean.Parser.Term.hole #[mkAtomFrom ref "_"]

/-- Convert a `Syntax.ident` into a `Lean.Parser.Term.id` node -/
def mkTermIdFromIdent (ident : Syntax) : Syntax :=
match ident with
| Syntax.ident _ _ _ _ => Syntax.node `Lean.Parser.Term.id #[ident, mkNullNode]
| _                    => unreachable!

/--
  Create a simple `Lean.Parser.Term.id` syntax using position
  information from `ref` and name `n`. By simple, we mean that
  `optional (explicitUniv <|> namedPattern)` is none.
  To refer to a specific constant, use `mkCTermIdFrom` instead. -/
def mkTermIdFrom (ref : Syntax) (n : Name) : Syntax :=
mkTermIdFromIdent (mkIdentFrom ref n)

/-- Variant of `mkTermIdFrom` that makes sure that the identifier cannot accidentally
    be captured. -/
def mkCTermIdFrom (ref : Syntax) (c : Name) : Syntax :=
mkTermIdFromIdent (mkCIdentFrom ref c)

def mkTermId (n : Name) : Syntax :=
mkTermIdFrom Syntax.missing n

def mkCTermId (c : Name) : Syntax :=
mkCTermIdFrom Syntax.missing c

def mkCAppStx (fn : Name) (args : Array Syntax) : Syntax :=
mkAppStx (mkCTermId fn) args

def mkStxLit (kind : SyntaxNodeKind) (val : String) (info : Option SourceInfo := none) : Syntax :=
let atom : Syntax := Syntax.atom info val;
Syntax.node kind #[atom]

def mkStxStrLit (val : String) (info : Option SourceInfo := none) : Syntax :=
mkStxLit strLitKind (repr val) info

def mkStxNumLit (val : String) (info : Option SourceInfo := none) : Syntax :=
mkStxLit numLitKind val info

end Lean

abbrev Array.getSepElems := @Array.getEvenElems
