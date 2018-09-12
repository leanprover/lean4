/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Term-level parsers
-/
prelude
import init.lean.parser.level

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

namespace term
/-- Access leading term -/
def get_leading : trailing_term_parser := read
instance : has_tokens get_leading := ⟨[]⟩
instance : has_view get_leading syntax := default _

@[derive parser.has_tokens parser.has_view]
def hole.parser : term_parser :=
node! hole [hole: symbol "_" max_prec]

@[derive parser.has_tokens parser.has_view]
def sort.parser : term_parser :=
node_choice! sort {"Sort":max_prec, "Sort*":max_prec, "Type":max_prec, "Type*":max_prec}

@[derive parser.has_tokens parser.has_view]
def leading.parser :=
any_of [
  ident,
  number,
  hole.parser,
  sort.parser
]

@[derive parser.has_tokens parser.has_view]
def sort_app.parser : trailing_term_parser :=
do { l ← get_leading, guard (syntax_node_kind.has_view.view sort l).is_some }  *>
node! sort_app [fn: get_leading, arg: monad_lift (level.parser max_prec)]

@[derive parser.has_tokens parser.has_view]
def app.parser : trailing_term_parser :=
node! app [fn: get_leading, arg: recurse max_prec]

@[derive parser.has_tokens parser.has_view]
def trailing.parser : trailing_term_parser :=
any_of [
  sort_app.parser,
  app.parser
]

end term

-- While term.parser does not actually read a command, it does share the same effect set
-- with command parsers, introducing the term-level recursion effect only for nested parsers
def term.parser (rbp := 0) : command_parser :=
pratt_parser term.leading.parser term.trailing.parser rbp <?> "term"

-- `[derive]` doesn't manage to derive these instances because of the parameter
instance term.parser.tokens (rbp) : has_tokens (term.parser rbp) :=
⟨has_tokens.tokens term.leading.parser ++ has_tokens.tokens term.trailing.parser⟩
instance term.parser.view (rbp) : has_view (term.parser rbp) syntax :=
default _

end parser
end lean
