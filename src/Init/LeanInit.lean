/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.String.Basic
import Init.Data.Array.Basic
import Init.Data.UInt
import Init.Data.Hashable

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

def Name.hash : Name → USize
| Name.anonymous => 1723
| Name.str p s h => h
| Name.num p v h => h

instance Name.hashable : Hashable Name := ⟨Name.hash⟩

@[export lean_name_hash] def Name.hashEx : Name → USize := Name.hash

@[export lean_name_mk_string]
def mkNameStr (p : Name) (s : String) : Name :=
Name.str p s $ mixHash (hash p) (hash s)

@[export lean_name_mk_numeral]
def mkNameNum (p : Name) (v : Nat) : Name :=
Name.num p v $ mixHash (hash p) (hash v)

def mkNameSimple (s : String) : Name :=
mkNameStr Name.anonymous s

@[extern "lean_name_eq"]
protected def Name.beq : (@& Name) → (@& Name) → Bool
| Name.anonymous,   Name.anonymous   => true
| Name.str p₁ s₁ _, Name.str p₂ s₂ _ => s₁ == s₂ && Name.beq p₁ p₂
| Name.num p₁ n₁ _, Name.num p₂ n₂ _ => n₁ == n₂ && Name.beq p₁ p₂
| _,                _                => false

instance : HasBeq Name := ⟨Name.beq⟩

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
| parser                         : Name → Nat → ParserDescrCore ParserKind.leading

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

end Syntax

end Lean
