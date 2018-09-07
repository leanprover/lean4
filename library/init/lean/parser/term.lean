/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Term-level parsers
-/
prelude
import init.lean.parser.token

namespace lean
namespace parser
open combinators parser.has_view monad_parsec

@[derive monad alternative monad_reader monad_state monad_parsec monad_except monad_rec monad_basic_read]
def command_parser_m := rec_t unit syntax basic_parser_m
abbreviation command_parser := command_parser_m syntax

@[derive monad alternative monad_reader monad_state monad_parsec monad_except monad_rec monad_basic_read]
def term_parser_m := rec_t nat syntax command_parser_m
abbreviation term_parser := term_parser_m syntax

/-- A term parser for a suffix or infix notation that accepts a preceding term. -/
@[derive monad alternative monad_reader monad_state monad_parsec monad_except monad_rec monad_basic_read]
def trailing_term_parser_m := reader_t syntax term_parser_m
abbreviation trailing_term_parser := trailing_term_parser_m syntax

/-- Access leading term -/
def leading : trailing_term_parser := read
instance : has_tokens leading := ⟨[]⟩
instance : has_view leading syntax := default _

@[derive parser.has_tokens parser.has_view]
def hole.parser : term_parser :=
node! hole [hole: symbol "_"]

@[derive parser.has_tokens parser.has_view]
def app.parser : trailing_term_parser :=
node! app [fn: leading, arg: recurse max_prec]

@[derive parser.has_tokens parser.has_view]
def leading.parser :=
any_of [
  hole.parser
]

@[derive parser.has_tokens parser.has_view]
def trailing.parser : trailing_term_parser :=
any_of [
  app.parser
]

/- Pratt parser -/

def curr_lbp : term_parser_m nat :=
do some tk ← monad_lift match_token | pure 0,
   pure tk.lbp

def trailing_loop (rbp : nat) : nat → syntax → term_parser
| 0 _ := error "unreachable"
| (n+1) left := do
  lbp ← curr_lbp,
  if rbp < lbp then do
    left ← trailing.parser.run left,
    trailing_loop n left
  else
    pure left

-- While term.parser does not actually read a command, it does share the same effect set
-- with command parsers, introducing the term-level recursion effect only for nested parsers
def term.parser : command_parser :=
with_recurse 0 $ λ rbp, do
  left ← leading.parser,
  n ← remaining,
  trailing_loop rbp (n+1) left

instance term.parser.tokens : has_tokens term.parser :=
⟨has_tokens.tokens leading.parser ++ has_tokens.tokens trailing.parser⟩
instance term.parser.view : has_view term.parser syntax :=
default _

end parser
end lean
