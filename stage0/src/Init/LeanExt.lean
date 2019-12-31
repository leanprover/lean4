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
inductive ParserDescr : ParserKind → Type
| andthen {k : ParserKind}       : ParserDescr k → ParserDescr k → ParserDescr k
| orelse  {k : ParserKind}       : ParserDescr k → ParserDescr k → ParserDescr k
| optional {k : ParserKind}      : ParserDescr k → ParserDescr k
| lookahead {k : ParserKind}     : ParserDescr k → ParserDescr k
| try {k : ParserKind}           : ParserDescr k → ParserDescr k
| many {k : ParserKind}          : ParserDescr k → ParserDescr k
| many1 {k : ParserKind}         : ParserDescr k → ParserDescr k
| sepBy {k : ParserKind}         : ParserDescr k → ParserDescr k → ParserDescr k
| sepBy1 {k : ParserKind}        : ParserDescr k → ParserDescr k → ParserDescr k
| node {k : ParserKind}          : Name → ParserDescr k → ParserDescr k
| symbol {k : ParserKind}        : String → Nat → ParserDescr k
| unicodeSymbol {k : ParserKind} : String → String → Nat → ParserDescr k
| pushLeading                    : ParserDescr ParserKind.trailing
| parser                         : Name → Nat → ParserDescr ParserKind.leading

end Lean
