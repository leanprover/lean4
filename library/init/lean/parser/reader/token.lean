/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Tokenizer for the Lean language

Even though our reader architecture does not statically depend on a tokenizer but works directly on
the input string, we still use a "tokenizer" parser in the Lean reader in some circumstances:
* to distinguish between identifiers and keywords
* for error recovery: advance until next command token
* ...?
-/

prelude
import init.lean.parser.reader.basic init.util

namespace lean.parser
namespace reader
open lean.parser.monad_parsec
open string

def match_token : basic_read_m (option token_config) :=
do st ← get,
   it ← left_over,
   -- the slowest longest prefix matcher on Earth
   pure $ st.tokens.foldl (λ acc tk,
     if tk.prefix.mk_iterator.is_prefix_of_remaining it then
       match acc with
       | some tk' := if tk.prefix > tk'.prefix then tk else tk'
       | none     := tk
     else acc) none

private def finish_comment_block_aux : nat → nat → basic_read_m unit
| nesting (n+1) :=
  str "/-" *> finish_comment_block_aux (nesting + 1) n <|>
  str "-/" *>
    (if nesting = 1 then pure ()
     else finish_comment_block_aux (nesting - 1) n) <|>
  any *> finish_comment_block_aux nesting n
| _ _ := error "unreachable"

def finish_comment_block (nesting := 1) : basic_read_m unit :=
do r ← remaining,
   finish_comment_block_aux nesting (r+1) <?> "end of comment block"

private def whitespace_aux : nat → basic_read_m unit
| (n+1) :=
do tk ← whitespace *> match_token,
   (match tk with
    | some ⟨"--", _⟩    := str "--" *> take_while' (= '\n') *> whitespace_aux n
    | some ⟨"/-", _⟩    := str "/-" *> finish_comment_block *> whitespace_aux n
    | _                 := pure ())
| 0 := error "unreachable"

variables {m : Type → Type} [has_monad_lift_t basic_read_m m]
local notation `reader` := m syntax
local notation `lift` := @monad_lift basic_read_m _ _ _

/-- Skip whitespace and comments. -/
def whitespace : basic_read_m substring :=
-- every `whitespace_aux` loop reads at least one char
do start ← left_over,
   whitespace_aux (start.remaining+1),
   stop ← left_over,
   pure ⟨start, stop⟩

def with_source_info [monad m] [monad_state reader_state m] [monad_parsec syntax m] {α : Type} (r : m α) : m (α × source_info) :=
do token_start ← reader_state.token_start <$> get,
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
def raw_symbol (sym : string) : reader :=
lift $ try $ do
  (_, info) ← with_source_info $ str sym,
  pure $ syntax.atom ⟨info, atomic_val.string sym⟩

instance raw_symbol.tokens (s) : reader.has_tokens (raw_symbol s : reader) := ⟨[]⟩
instance raw_symbol.view (s) : reader.has_view (raw_symbol s : reader) syntax := default _

@[pattern] def base10_lit : syntax_node_kind := ⟨`lean.parser.reader.base10_lit⟩

--TODO(Sebastian): other bases
private def number' : basic_read_m (source_info → syntax) :=
do num ← take_while1 char.is_digit,
   pure $ λ i, syntax.node ⟨base10_lit, [syntax.atom ⟨i, atomic_val.string num⟩]⟩

private def ident' : basic_read_m (source_info → syntax) :=
do n ← identifier,
   pure $ λ i, syntax.ident ⟨i, n, none, none⟩

private def symbol' : basic_read_m (source_info → syntax) :=
do tk ← match_token,
   match tk with
   -- constant-length token
   | some ⟨tk, none⟩   :=
     do str tk,
         pure $ λ i, syntax.atom ⟨some i, atomic_val.string tk⟩
   -- variable-length token
   | some ⟨tk, some r⟩ := error "not implemented" --str tk *> monad_parsec.lift r
   | none              := error

def token : basic_read_m syntax :=
do (r, i) ← with_source_info $ do {
     -- NOTE the order: if a token is both a symbol and a valid identifier (i.e. a keyword),
     -- we want it to be recognized as a symbol
     f::_ ← longest_match [symbol', ident', number'] | failure,
     pure f
   },
   pure (r i)

--TODO(Sebastian): error messages
def symbol (sym : string) : reader :=
lift $ try $ do
  it ← left_over,
  stx@(syntax.atom ⟨_, atomic_val.string sym'⟩) ← token | error "" (dlist.singleton (repr sym)) it,
  when (sym ≠ sym') $
    error "" (dlist.singleton (repr sym)) it,
  pure stx

instance symbol.tokens (sym : string) : reader.has_tokens (symbol sym : reader) :=
⟨[⟨sym, none⟩]⟩
instance symbol.view (s) : reader.has_view (symbol s : reader) syntax := default _

def number : reader :=
lift $ try $ do
  it ← left_over,
  stx@(syntax.node ⟨base10_lit, _⟩) ← token | error "" (dlist.singleton "number") it,
  pure stx

instance number.tokens : reader.has_tokens (number : reader) := ⟨[]⟩
instance number.view : reader.has_view (number : reader) syntax := default _

def ident : reader :=
lift $ try $ do
  it ← left_over,
  stx@(syntax.ident _) ← token | error "" (dlist.singleton "identifier") it,
  pure stx

instance ident.tokens : reader.has_tokens (ident : reader) := ⟨[]⟩
instance ident.view : reader.has_view (ident : reader) syntax := default _

end «reader»
end lean.parser
