/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Term-level parsers and macros
-/
prelude
import init.lean.parser.token

namespace lean
namespace parser
open combinators parser.has_view

@[derive monad alternative monad_reader monad_state monad_parsec monad_except monad_rec monad_basic_read]
def command_parser_m := rec_t syntax basic_parser_m
abbreviation command_parser := command_parser_m syntax

@[derive monad alternative monad_reader monad_state monad_parsec monad_except monad_rec monad_basic_read]
def term_parser_m := rec_t syntax command_parser_m
abbreviation term_parser := term_parser_m syntax

@[derive parser.has_tokens parser.has_view]
def hole.parser : term_parser :=
node! hole [hole: symbol "_"]

@[derive parser.has_tokens parser.has_view]
-- While term.parser does not actually read a command, it does share the same effect set
-- with command parsers, introducing the term-level recursion effect only for nested parsers
def term.parser : command_parser :=
with_recurse $ any_of [
  hole.parser
]

end parser
end lean
