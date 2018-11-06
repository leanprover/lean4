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
variables [monad base_m] [monad_basic_parser base_m] [monad_parsec syntax base_m] [monad_reader parser_config base_m]

local notation `m` := rec_t nat syntax base_m
local notation `parser` := m syntax

def curr_lbp : m nat :=
do except.ok tk ← monad_lift peek_token | pure 0,
   match tk with
   | syntax.atom ⟨_, sym⟩ := do
     cfg ← read,
     some ⟨_, tk_cfg⟩ ← pure (cfg.tokens.match_prefix sym.mk_iterator) | error "curr_lbp: unreachable",
     pure tk_cfg.lbp
   | syntax.raw_node {kind := @number, ..} := pure max_prec
   | syntax.raw_node {kind := @ident, ..} := pure max_prec
   | syntax.raw_node {kind := @string_lit, ..} := pure max_prec
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
variables (leading : m syntax) (trailing : reader_t syntax m syntax) (p : m syntax)

def pratt_parser : base_m syntax :=
rec_t.run_parsec p $ λ rbp, do
left ← leading,
n ← remaining,
trailing_loop trailing rbp (n+1) left

instance pratt_parser.tokens [has_tokens leading] [has_tokens trailing] : has_tokens (pratt_parser leading trailing p) :=
⟨has_tokens.tokens leading ++ has_tokens.tokens trailing⟩
instance pratt_parser.view : has_view syntax (pratt_parser leading trailing p) :=
default _

end lean.parser
