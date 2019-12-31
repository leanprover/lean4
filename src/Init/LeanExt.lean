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
inductive ParserDescr (kind : ParserKind := ParserKind.leading)
| andthen       : ParserDescr → ParserDescr → ParserDescr
| orelse        : ParserDescr → ParserDescr → ParserDescr
| optional      : ParserDescr → ParserDescr
| lookahead     : ParserDescr → ParserDescr
| try           : ParserDescr → ParserDescr
| many          : ParserDescr → ParserDescr
| many1         : ParserDescr → ParserDescr
| sepBy         : ParserDescr → ParserDescr → ParserDescr
| sepBy1        : ParserDescr → ParserDescr → ParserDescr
| symbol        : String → Nat → ParserDescr
| unicodeSymbol : String → String → Nat → ParserDescr
| parser        : Name → ParserDescr

end Lean
