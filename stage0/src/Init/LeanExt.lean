/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.String.Basic
import Init.Data.UInt

namespace Lean
/-
Basic Lean types used to implement basic extensions.
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
| symbol {k : ParserKind}        : String → Nat → ParserDescrCore k
| unicodeSymbol {k : ParserKind} : String → String → Nat → ParserDescrCore k
| tacticSymbol                   : String → ParserDescrCore ParserKind.leading
| pushLeading                    : ParserDescrCore ParserKind.trailing
| parser                         : Name → Nat → ParserDescrCore ParserKind.leading

instance ParserDescrCore.inhabited {k} : Inhabited (ParserDescrCore k) := ⟨ParserDescrCore.symbol "" 0⟩

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
@[matchPattern] abbrev ParserDescr.tacticSymbol := @ParserDescrCore.tacticSymbol
@[matchPattern] abbrev ParserDescr.unicodeSymbol := @ParserDescrCore.unicodeSymbol
@[matchPattern] abbrev ParserDescr.pushLeading := @ParserDescrCore.pushLeading
@[matchPattern] abbrev ParserDescr.parser := @ParserDescrCore.parser

end Lean
