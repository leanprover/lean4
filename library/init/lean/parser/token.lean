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
import init.lean.parser.basic

namespace lean
namespace parser
open lean.parser.monad_parsec
open string

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
do tk ← whitespace *> match_token,
   (match tk with
    | some ⟨"--", _⟩    := str "--" *> take_while' (= '\n') *> whitespace_aux n
    | some ⟨"/-", _⟩    := str "/-" *> finish_comment_block *> whitespace_aux n
    | _                 := pure ())
| 0 := error "unreachable"

abbreviation monad_basic_read := has_monad_lift_t basic_parser_m
variables {m : Type → Type} [monad_basic_read m]
local notation `parser` := m syntax
local notation `lift` := @monad_lift basic_parser_m _ _ _

/-- Skip whitespace and comments. -/
def whitespace : basic_parser_m substring :=
-- every `whitespace_aux` loop reads at least one char
do start ← left_over,
   whitespace_aux (start.remaining+1),
   stop ← left_over,
   pure ⟨start, stop⟩

def with_source_info [monad m] [monad_state parser_state m] [monad_parsec syntax m] {α : Type} (r : m α) : m (α × source_info) :=
do token_start ← parser_state.token_start <$> get,
   lift whitespace,
   it ← left_over,
   a ← r,
   -- TODO(Sebastian): less greedy, more natural whitespace assignement
   -- E.g. only read up to the next line break
   trailing ← lift whitespace,
   it2 ← left_over,
   modify $ λ st, {st with token_start := it2},
   pure (a, ⟨⟨token_start, it⟩, it.offset, trailing⟩)

/-- Match a string literally without consulting the token table. -/
def raw_symbol (sym : string) : parser :=
lift $ try $ do
  (_, info) ← with_source_info $ str sym,
  pure $ syntax.atom ⟨info, atomic_val.string sym⟩

instance raw_symbol.tokens (s) : parser.has_tokens (raw_symbol s : parser) := ⟨[]⟩
instance raw_symbol.view (s) : parser.has_view (raw_symbol s : parser) syntax := default _

@[pattern] def base10_lit : syntax_node_kind := ⟨`lean.parser.parser.base10_lit⟩

--TODO(Sebastian): other bases
private def number' : basic_parser_m (source_info → syntax) :=
do num ← take_while1 char.is_digit,
   pure $ λ i, syntax.node ⟨base10_lit, [syntax.atom ⟨i, atomic_val.string num⟩]⟩

private def ident' : basic_parser_m (source_info → syntax) :=
do n ← identifier,
   pure $ λ i, syntax.ident ⟨i, n, none, none⟩

private def symbol' : basic_parser_m (source_info → syntax) :=
do tk ← match_token,
   match tk with
   -- constant-length token
   | some ⟨tk, none⟩   :=
     do str tk,
        pure $ λ i, syntax.atom ⟨some i, atomic_val.string tk⟩
   -- variable-length token
   | some ⟨tk, some r⟩ := error "not implemented" --str tk *> monad_parsec.lift r
   | none              := error

def token : basic_parser_m syntax :=
do (r, i) ← with_source_info $ do {
     -- NOTE the order: if a token is both a symbol and a valid identifier (i.e. a keyword),
     -- we want it to be recognized as a symbol
     f::_ ← longest_match [symbol', ident', number'] | failure,
     pure f
   },
   pure (r i)

--TODO(Sebastian): error messages
def symbol (sym : string) : parser :=
lift $ try $ do
  it ← left_over,
  stx@(syntax.atom ⟨_, atomic_val.string sym'⟩) ← token | error "" (dlist.singleton (repr sym)) it,
  when (sym ≠ sym') $
    error "" (dlist.singleton (repr sym)) it,
  pure stx

instance symbol.tokens (sym : string) : parser.has_tokens (symbol sym : parser) :=
⟨[⟨sym, none⟩]⟩
instance symbol.view (s) : parser.has_view (symbol s : parser) syntax := default _

def number : parser :=
lift $ try $ do
  it ← left_over,
  stx@(syntax.node ⟨base10_lit, _⟩) ← token | error "" (dlist.singleton "number") it,
  pure stx

instance number.tokens : parser.has_tokens (number : parser) := ⟨[]⟩
instance number.view : parser.has_view (number : parser) syntax := default _

def ident : parser :=
lift $ try $ do
  it ← left_over,
  stx@(syntax.ident _) ← token | error "" (dlist.singleton "identifier") it,
  pure stx

instance ident.tokens : parser.has_tokens (ident : parser) := ⟨[]⟩
instance ident.view : parser.has_view (ident : parser) syntax := default _

end «parser»
end lean
