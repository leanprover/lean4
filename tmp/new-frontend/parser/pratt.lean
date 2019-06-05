/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

A Combinator for building Pratt parsers
-/
prelude
import init.lean.parser.token

namespace Lean.Parser
open MonadParsec Combinators

variables {baseM : Type → Type}
variables [Monad baseM] [monadBasicParser baseM] [MonadParsec Syntax baseM] [MonadReader ParserConfig baseM]

local notation `m` := RecT Nat Syntax baseM
local notation `Parser` := m Syntax

def currLbp : m Nat :=
do Except.ok tk ← monadLift peekToken | pure 0,
   match tk with
   | Syntax.atom ⟨_, sym⟩ := do
     cfg ← read,
     some ⟨_, tkCfg⟩ ← pure (cfg.tokens.oldMatchPrefix sym.mkOldIterator) | error "currLbp: unreachable",
     pure tkCfg.lbp
   | Syntax.ident _ := pure maxPrec
   | Syntax.rawNode {kind := @number, ..} := pure maxPrec
   | Syntax.rawNode {kind := @stringLit, ..} := pure maxPrec
   | _ := error "currLbp: unknown token kind"

private def trailingLoop (trailing : ReaderT Syntax m Syntax) (rbp : Nat) : Nat → Syntax → Parser
| 0 _ := error "unreachable"
| (n+1) left := do
lbp ← currLbp,
if rbp < lbp then do
  left ← trailing.run left,
  trailingLoop n left
else
  pure left

variables [MonadExcept (Parsec.Message Syntax) baseM] [Alternative baseM]
variables (leading : m Syntax) (trailing : ReaderT Syntax m Syntax) (p : m Syntax)

def prattParser : baseM Syntax :=
RecT.runParsec p $ λ rbp, do
left ← leading,
n ← remaining,
trailingLoop trailing rbp (n+1) left

instance prattParser.tokens [HasTokens leading] [HasTokens trailing] : HasTokens (prattParser leading trailing p) :=
⟨HasTokens.tokens leading ++ HasTokens.tokens trailing⟩
instance prattParser.View : HasView Syntax (prattParser leading trailing p) :=
default _

end Lean.Parser
