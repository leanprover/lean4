/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Tokenizer for the Lean language

Even though our parser architecture does not statically depend on a tokenizer but works directly on
the input string, we still use a "tokenizer" parser in the Lean parser in some circumstances:
* to distinguish between identifiers and keywords
* for error recovery: advance until next command token
* ...?
-/

prelude
import init.lean.parser.combinators

namespace lean
namespace parser
open monad_parsec combinators string has_view

def match_token : basic_parser_m (option token_config) :=
do st ← get,
   it ← left_over,
   pure $ prod.snd <$> st.tokens.match_prefix it

private def finish_comment_block_aux : nat → nat → basic_parser_m unit
| nesting (n+1) :=
  str "/-" *> finish_comment_block_aux (nesting + 1) n <|>
  str "-/" *>
    (if nesting = 1 then pure ()
     else finish_comment_block_aux (nesting - 1) n) <|>
  any *> finish_comment_block_aux nesting n
| _ _ := error "unreachable"

def finish_comment_block (nesting := 1) : basic_parser_m unit :=
do r ← remaining,
   finish_comment_block_aux nesting (r+1) <?> "end of comment block"

private def whitespace_aux : nat → basic_parser_m unit
| (n+1) :=
do whitespace,
   str "--" *> take_while' (= '\n') *> whitespace_aux n <|>
   -- a "/--" doc comment is an actual token, not whitespace
   try (str "/-" *> not_followed_by (str "-")) *> finish_comment_block *> whitespace_aux n <|>
   pure ()
| 0 := error "unreachable"

variables {m : Type → Type}
local notation `parser` := m syntax
local notation `lift` := @monad_lift basic_parser_m _ _ _

/-- Skip whitespace and comments. -/
def whitespace : basic_parser_m unit :=
hidden $ do
  start ← left_over,
  -- every `whitespace_aux` loop reads at least one char
  whitespace_aux (start.remaining+1)

section
variables [monad m] [monad_parsec syntax m]

def as_substring {α : Type} (p : m α) : m substring :=
do start ← left_over,
   p,
   stop ← left_over,
   pure ⟨start, stop⟩

variables [monad_state parser_state m] [monad_basic_read m]

def with_source_info {α : Type} (r : m α) (trailing_ws := tt) : m (α × source_info) :=
do it ← left_over,
   let leading : substring := ⟨it, it⟩, -- NOTE: will be adjusted by `syntax.update_leading`
   a ← r,
   -- TODO(Sebastian): less greedy, more natural whitespace assignment
   -- E.g. only read up to the next line break
   trailing ← lift $ as_substring $ if trailing_ws then whitespace else pure (),
   it2 ← left_over,
   pure (a, ⟨leading, it.offset, trailing⟩)

/-- Match an arbitrary parser and return the consumed string in a `syntax.atom`. -/
def raw {α : Type} (p : m α) (trailing_ws := ff) : parser :=
try $ do
  (ss, info) ← with_source_info (as_substring p) trailing_ws,
  pure $ syntax.atom ⟨info, ss.to_string⟩

instance raw.tokens {α} (p : m α) (t) : parser.has_tokens (raw p t : parser) := default _
instance raw.view {α} (p : m α) (t) : parser.has_view (raw p t : parser) syntax := default _

end

@[pattern] def base10_lit : syntax_node_kind := ⟨`lean.parser.base10_lit⟩

--TODO(Sebastian): other bases
private def number' : basic_parser_m (source_info → syntax) :=
do num ← take_while1 char.is_digit,
   pure $ λ i, syntax.node ⟨base10_lit, [syntax.atom ⟨i, num⟩]⟩

set_option class.instance_max_depth 200

@[derive has_tokens has_view]
def ident_part.parser : basic_parser_m syntax :=
node_choice! ident_part {
  escaped: node! ident_part_escaped [
    esc_begin: raw $ ch id_begin_escape,
    escaped: raw $ take_until1 is_id_end_escape,
    esc_end: raw $ ch id_end_escape
  ],
  default: lookahead (satisfy is_id_first) *> raw (take_while is_id_rest)
}

@[derive has_tokens has_view]
def ident_suffix.parser : rec_t unit syntax basic_parser_m syntax :=
-- consume '.' only when followed by a character starting an ident_part
try (lookahead (ch '.' *> (ch id_begin_escape *> pure () <|> satisfy is_id_first *> pure ()))) *>
node! ident_suffix [«.»: raw $ ch '.', ident: recurse ()]

private mutual def update_trailing, update_trailing_lst
with update_trailing : substring → syntax → syntax
| trailing (syntax.atom a@⟨some info, _⟩) := syntax.atom {a with info := some {info with trailing := trailing}}
| trailing (syntax.node n@⟨k, args⟩) := syntax.node {n with args := update_trailing_lst trailing args}
| trailing stx := stx
with update_trailing_lst : substring → list syntax → list syntax
| trailing [] := []
| trailing [stx] := [update_trailing trailing stx]
| trailing (stx::stxs) := stx :: update_trailing_lst trailing stxs

def ident' : basic_parser_m (source_info → syntax) :=
do stx ← with_recurse () $ λ _, node! ident [part: monad_lift ident_part.parser, suffix: optional ident_suffix.parser],
   pure $ λ info, update_trailing info.trailing stx

private def symbol' : basic_parser_m (source_info → syntax) :=
do tk ← match_token,
   match tk with
   -- constant-length token
   | some ⟨tk, _, none⟩   :=
     do str tk,
        pure $ λ i, syntax.atom ⟨some i, tk⟩
   -- variable-length token
   | some ⟨tk, _, some r⟩ := error "symbol': not implemented" --str tk *> monad_parsec.lift r
   | none                 := monad_parsec.eoi *> error "end of file" <|> error "token"

def token : basic_parser_m syntax :=
do (r, i) ← with_source_info $ do {
     -- NOTE the order: if a token is both a symbol and a valid identifier (i.e. a keyword),
     -- we want it to be recognized as a symbol
     f::_ ← longest_match [symbol', ident'] <|> list.ret <$> number' | error "token: unreachable",
     pure f
   },
   pure (r i)

variable [monad_basic_read m]

def symbol (sym : string) (lbp := 0) : parser :=
lift $ try $ do {
  it ← left_over,
  stx@(syntax.atom ⟨_, sym'⟩) ← token | error "" (dlist.singleton (repr sym)) it,
  when (sym ≠ sym') $
    error "" (dlist.singleton (repr sym)) it,
  pure stx
} <?> repr sym

instance symbol.tokens (sym lbp) : parser.has_tokens (symbol sym lbp : parser) :=
⟨λ t, t.insert sym ⟨sym, lbp, none⟩⟩
instance symbol.view (sym lbp) : parser.has_view (symbol sym lbp : parser) syntax := default _

def number : parser :=
lift $ try $ do {
  it ← left_over,
  stx@(syntax.node ⟨base10_lit, _⟩) ← token | error "" (dlist.singleton "number") it,
  pure stx
} <?> "number"

instance number.tokens : parser.has_tokens (number : parser) := default _
instance number.view : parser.has_view (number : parser) syntax := default _

def ident.parser : parser :=
lift $ try $ do {
  it ← left_over,
  stx@(syntax.node ⟨ident, _⟩) ← token | error "" (dlist.singleton "identifier") it,
  pure stx
} <?> "identifier"

instance ident.parser.tokens : parser.has_tokens (ident.parser : parser) := default _
instance ident.parser.view : parser.has_view (ident.parser : parser) syntax := default _

/-- Check if the following token is the symbol _or_ identifier `sym`. Useful for
    parsing local tokens that have not been added to the token table (but may have
    been so by some unrelated code).

    For example, the universe `max` function is parsed using this combinator so that
    it can still be used as an identifier outside of universes (but registering it
    as a token in a term syntax would not break the universe parser). -/
def symbol_or_ident (sym : string) : parser :=
lift $ try $ do
  it ← left_over,
  stx ← token,
  let sym' := match stx with
  | syntax.atom ⟨_, sym'⟩ := some sym'
  | syntax.node ⟨ident, _⟩ :=
    (match syntax_node_kind.has_view.view ident stx with
     | some {part := ident_part.view.default (syntax.atom ⟨_, sym'⟩),
             suffix := optional_view.none} := some sym'
     | _ := none)
  | _ := none,
  when (sym' ≠ some sym) $
    error "" (dlist.singleton (repr sym)) it,
  pure stx

instance symbol_or_ident.tokens (sym) : parser.has_tokens (symbol_or_ident sym : parser) :=
default _
instance symbol_or_ident.view (sym) : parser.has_view (symbol_or_ident sym : parser) syntax := default _

end «parser»
end lean
