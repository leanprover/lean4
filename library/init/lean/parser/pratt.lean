/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

A combinator for building Pratt parsers
-/
prelude
import init.lean.parser.token

namespace lean.parser
open monadParsec combinators

variables {baseM : Type → Type}
variables [monad baseM] [monadBasicParser baseM] [monadParsec syntax baseM] [monadReader parserConfig baseM]

local notation `m` := recT nat syntax baseM
local notation `parser` := m syntax

def currLbp : m nat :=
do except.ok tk ← monadLift peekToken | pure 0,
   match tk with
   | syntax.atom ⟨_, sym⟩ := do
     cfg ← read,
     some ⟨_, tkCfg⟩ ← pure (cfg.tokens.matchPrefix sym.mkIterator) | error "currLbp: unreachable",
     pure tkCfg.lbp
   | syntax.ident _ := pure maxPrec
   | syntax.rawNode {kind := @number, ..} := pure maxPrec
   | syntax.rawNode {kind := @stringLit, ..} := pure maxPrec
   | _ := error "currLbp: unknown token kind"

private def trailingLoop (trailing : readerT syntax m syntax) (rbp : nat) : nat → syntax → parser
| 0 _ := error "unreachable"
| (n+1) left := do
lbp ← currLbp,
if rbp < lbp then do
  left ← trailing.run left,
  trailingLoop n left
else
  pure left

variables [monadExcept (parsec.message syntax) baseM] [alternative baseM]
variables (leading : m syntax) (trailing : readerT syntax m syntax) (p : m syntax)

def prattParser : baseM syntax :=
recT.runParsec p $ λ rbp, do
left ← leading,
n ← remaining,
trailingLoop trailing rbp (n+1) left

instance prattParser.tokens [hasTokens leading] [hasTokens trailing] : hasTokens (prattParser leading trailing p) :=
⟨hasTokens.tokens leading ++ hasTokens.tokens trailing⟩
instance prattParser.view : hasView syntax (prattParser leading trailing p) :=
default _

end lean.parser
