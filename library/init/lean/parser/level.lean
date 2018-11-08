/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Level-level parsers
-/
prelude
import init.lean.parser.pratt

namespace lean
namespace parser
open combinators parser.has_view monad_parsec

@[derive monad alternative monad_reader monad_parsec monad_except monad_rec monad_basic_parser]
def level_parser_m := rec_t nat syntax basic_parser_m
abbreviation level_parser := level_parser_m syntax

/-- A level parser for a suffix or infix notation that accepts a preceding term level. -/
@[derive monad alternative monad_reader monad_parsec monad_except monad_rec monad_basic_parser]
def trailing_level_parser_m := reader_t syntax level_parser_m
abbreviation trailing_level_parser := trailing_level_parser_m syntax

instance trailing_level_parser_coe : has_coe level_parser trailing_level_parser :=
⟨λ x _, x⟩

@[derive parser.has_tokens parser.has_view]
def level.parser (rbp := 0) : level_parser :=
recurse rbp <?> "universe level"

namespace level
/-- Access leading term -/
def get_leading : trailing_level_parser := read
instance : has_tokens get_leading := default _
instance : has_view syntax get_leading := default _

@[derive parser.has_tokens parser.has_view]
def paren.parser : level_parser :=
node! «paren» ["(":max_prec, inner: level.parser 0, ")"]

@[derive parser.has_tokens parser.has_view]
def leading.parser : level_parser :=
node_choice! leading {
  max: symbol_or_ident "max",
  imax: symbol_or_ident "imax",
  hole: symbol "_" max_prec,
  paren: paren.parser,
  lit: number.parser,
  var: ident.parser
}

@[derive parser.has_tokens parser.has_view]
def app.parser : trailing_level_parser :=
node! app [fn: get_leading, arg: level.parser max_prec]

@[derive parser.has_tokens parser.has_view]
def add_lit.parser : trailing_level_parser :=
node! add_lit [lhs: get_leading, "+", rhs: number.parser]

@[derive parser.has_tokens parser.has_view]
def trailing.parser : trailing_level_parser :=
node_choice! trailing {
  app: app.parser,
  add_lit: add_lit.parser
}
end level

@[derive parser.has_tokens parser.has_view]
def level_parser.run (p : level_parser) : basic_parser :=
pratt_parser level.leading.parser level.trailing.parser p

instance level_parser_coe : has_coe level_parser basic_parser :=
⟨level_parser.run⟩

end parser
end lean
