/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

A combinator for building Pratt parsers
-/
prelude
import init.lean.parser.token

namespace lean.parser
open monad_parsec combinators

variables {base_m : Type → Type}
variables [monad base_m] [monad_basic_read base_m] [monad_state parser_state base_m] [monad_parsec syntax base_m]

local notation `m` := rec_t nat syntax base_m
local notation `parser` := m syntax

def curr_lbp : m nat :=
do st ← get,
   except.ok tk ← (monad_lift $ observing $ lookahead token) <* put st | pure 0 <* put st,
   match tk with
   | syntax.atom ⟨_, sym⟩ := do
     st ← get,
     some ⟨_, tk_cfg⟩ ← pure (st.tokens.match_prefix sym.mk_iterator) | error "curr_lbp: unreachable",
     pure tk_cfg.lbp
   | syntax.node ⟨base10_lit, _⟩ := pure max_prec
   | syntax.node ⟨id, _⟩ := pure max_prec
   | _ := error "curr_lbp: unknown token kind"

private def trailing_loop (trailing : reader_t syntax m syntax) (rbp : nat) : nat → syntax → parser
| 0 _ := error "unreachable"
| (n+1) left := do
lbp ← curr_lbp,
if rbp < lbp then do
  left ← trailing.run left,
  trailing_loop n left
else
  pure left

variables [monad_except (parsec.message syntax) base_m] [alternative base_m]
variables (leading : m syntax) (trailing : reader_t syntax m syntax)

def pratt_parser (rbp := 0) : base_m syntax :=
with_recurse rbp $ λ rbp, do
left ← leading,
n ← remaining,
trailing_loop trailing rbp (n+1) left

instance pratt_parser.tokens [has_tokens leading] [has_tokens trailing] : has_tokens (pratt_parser leading trailing) :=
⟨has_tokens.tokens leading ++ has_tokens.tokens trailing⟩
instance pratt_parser.view : has_view (pratt_parser leading trailing) syntax :=
default _

end lean.parser
