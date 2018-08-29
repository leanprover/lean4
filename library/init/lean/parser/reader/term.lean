/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Term-level readers and macros
-/
prelude
import init.lean.parser.reader.token

namespace lean.parser
namespace reader
open combinators reader.has_view

@[derive monad alternative monad_reader monad_state monad_parsec monad_except monad_rec]
abbreviation command_read_m := rec_t syntax basic_read_m
abbreviation command_reader := command_read_m syntax

@[derive monad alternative monad_reader monad_state monad_parsec monad_except monad_rec]
abbreviation term_read_m := rec_t syntax command_read_m
abbreviation term_reader := term_read_m syntax

@[derive reader.has_tokens reader.has_view]
def hole.reader : term_reader :=
node! hole [hole: symbol "_"]

@[derive reader.has_tokens reader.has_view]
-- While term.reader does not actually read a command, it does share the same effect set
-- with command readers, introducing the term-level recursion effect only for nested readers
def term.reader : command_reader :=
with_recurse $ any_of [
  hole.reader
]

end reader
end lean.parser
