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
do cfg ← read,
   it ← left_over,
   pure $ prod.snd <$> cfg.tokens.match_prefix it

private def finish_comment_block_aux : nat → nat → basic_parser_m unit
| nesting (n+1) :=
  str "/-" *> finish_comment_block_aux (nesting + 1) n
  <|>
  str "-/" *>
  if nesting = 1 then pure ()
  else finish_comment_block_aux (nesting - 1) n
  <|>
  any *> finish_comment_block_aux nesting n
| _ _ := error "unreachable"

def finish_comment_block (nesting := 1) : basic_parser_m unit :=
do r ← remaining,
   finish_comment_block_aux nesting (r+1) <?> "end of comment block"

private def whitespace_aux : nat → basic_parser_m unit
| (n+1) :=
do whitespace,
   str "--" *> take_while' (≠ '\n') *> whitespace_aux n
   <|>
   -- a "/--" doc comment is an actual token, not whitespace
   try (str "/-" *> not_followed_by (str "-")) *> finish_comment_block *> whitespace_aux n
   <|>
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

@[inline] def as_substring {α : Type} (p : m α) : m substring :=
do start ← left_over,
   p,
   stop ← left_over,
   pure ⟨start, stop⟩

variables [monad_state parser_state m] [monad_basic_parser m]

private mutual def update_trailing, update_trailing_lst
with update_trailing : substring → syntax → syntax
| trailing (syntax.atom a@⟨some info, _⟩) := syntax.atom {a with info := some {info with trailing := trailing}}
| trailing (syntax.node n@⟨k, args⟩) := syntax.node {n with args := update_trailing_lst trailing args}
| trailing stx := stx
with update_trailing_lst : substring → list syntax → list syntax
| trailing [] := []
| trailing [stx] := [update_trailing trailing stx]
| trailing (stx::stxs) := stx :: update_trailing_lst trailing stxs

def with_trailing (stx : syntax) : m syntax :=
do -- TODO(Sebastian): less greedy, more natural whitespace assignment
   -- E.g. only read up to the next line break
   trailing ← lift $ as_substring $ whitespace,
   pure $ update_trailing trailing stx

def mk_raw_res (start stop : string.iterator) : syntax :=
let ss : substring := ⟨start, stop⟩ in
syntax.atom ⟨some {leading := ⟨start, start⟩, pos := start.offset, trailing := ⟨stop, stop⟩}, ss.to_string⟩

/-- Match an arbitrary parser and return the consumed string in a `syntax.atom`. -/
@[inline] def raw {α : Type} (p : m α) (trailing_ws := ff) : parser :=
try $ do
  start ← left_over,
  p,
  stop ← left_over,
  let stx := mk_raw_res start stop,
  if trailing_ws then with_trailing stx else pure stx

instance raw.tokens {α} (p : m α) (t) : parser.has_tokens (raw p t : parser) := default _
instance raw.view {α} (p : m α) (t) : parser.has_view (raw p t : parser) (option syntax_atom) :=
{ view := λ stx, match stx with
  | syntax.atom atom := some atom
  | _                := none,
  review := λ a, (syntax.atom <$> a).get_or_else syntax.missing }

/-- Like `raw (str s)`, but default to `s` in views. -/
@[derive has_tokens has_view]
def raw_str (s : string) (trailing_ws := ff) : parser :=
raw (str s) trailing_ws

instance raw_str.view_default (s) (t) : parser.has_view_default (raw_str s t : parser) (option syntax_atom) (some {val := s}) :=
⟨⟩

end

set_option class.instance_max_depth 200

@[derive has_tokens has_view]
def ident_part.parser : basic_parser_m syntax :=
node_choice! ident_part {
  escaped: node! ident_part_escaped [
    esc_begin: raw_str id_begin_escape.to_string,
    escaped: raw $ take_until1 is_id_end_escape,
    esc_end: raw_str id_end_escape.to_string,
  ],
  default: raw $ satisfy is_id_first *> take_while is_id_rest
}

@[derive has_tokens has_view]
def ident_suffix.parser : rec_t unit syntax basic_parser_m syntax :=
-- consume '.' only when followed by a character starting an ident_part
try (lookahead (ch '.' *> (ch id_begin_escape <|> satisfy is_id_first)))
*> node! ident_suffix [«.»: raw_str ".", ident: recurse ()]

def ident'' : rec_t unit syntax basic_parser_m syntax :=
node! ident [part: monad_lift ident_part.parser, suffix: optional ident_suffix.parser]

private def ident' : basic_parser_m syntax :=
rec_t.run_parsec ident'' $ λ _, ident''

private def symbol' : basic_parser_m syntax :=
do tk ← match_token,
   match tk with
   -- constant-length token
   | some ⟨tk, _, none⟩   :=
     raw (str tk)
   -- variable-length token
   | some ⟨tk, _, some r⟩ := error "symbol': not implemented" --str tk *> monad_parsec.lift r
   | none                 := monad_parsec.eoi *> error "end of file" <|> error "token"

--TODO(Sebastian): other bases
def number' : basic_parser :=
node_choice! number {
  base10: raw (take_while1 char.is_digit),
}

def token : basic_parser :=
do it ← left_over,
   cache ← get_cache,
   -- NOTE: using `catch` instead of `<|>` so that error messages from the second block are preferred
   catch (do
     -- check token cache
     some tkc ← pure cache.token_cache | failure,
     guard (it.offset = tkc.start_it.offset),
     -- hackishly update parsec position
     monad_parsec.lift (λ it, parsec.result.ok () tkc.stop_it none),
     pure tkc.tk
   ) (λ _, do
     -- cache failed, update cache

     -- NOTE the order: if a token is both a symbol and a valid identifier (i.e. a keyword),
     -- we want it to be recognized as a symbol
     tk::_ ← monad_parsec.longest_match [symbol', ident'] <|> list.ret <$> number' | error "token: unreachable",
     tk ← with_trailing tk,
     new_it ← left_over,
     put_cache {cache with token_cache := some ⟨it, new_it, tk⟩},
     pure tk
   )

variable [monad_basic_parser m]

def symbol (sym : string) (lbp := 0) : parser :=
let sym := sym.trim in
lift $ try $ do {
  it ← left_over,
  stx@(syntax.atom ⟨_, sym'⟩) ← token | error "" (dlist.singleton sym) it,
  when (sym ≠ sym') $
    error ("token " ++ sym') (dlist.singleton sym) it,
  pure stx
} <?> sym

instance symbol.tokens (sym lbp) : parser.has_tokens (symbol sym lbp : parser) :=
⟨[⟨sym.trim, lbp, none⟩]⟩
instance symbol.view (sym lbp) : parser.has_view (symbol sym lbp : parser) (option syntax_atom) :=
{ view := λ stx, match stx with
  | syntax.atom atom := some atom
  | _                := none,
  review := λ a, (syntax.atom <$> a).get_or_else syntax.missing }
instance symbol.view_default (sym lbp) : parser.has_view_default (symbol sym lbp : parser) _
  (some {info := none, val := sym.trim}) := ⟨⟩

def number.parser : parser :=
lift $ try $ do {
  it ← left_over,
  stx ← token,
  some _ ← pure $ try_view number stx | error "" (dlist.singleton "number") it,
  pure stx
} <?> "number"

instance number.parser.tokens : parser.has_tokens (number.parser : parser) := default _
instance number.parser.view : parser.has_view (number.parser : parser) number.view :=
{..number.has_view}

def number.view.to_nat : number.view → nat
| (number.view.base10 (some atom)) := atom.val.to_nat
| _ := 1138 -- should never happen, but let's still choose a grep-able number

def number.view.of_nat (n : nat) : number.view :=
number.view.base10 (some {val := to_string n})

def ident.parser : parser :=
lift $ try $ do {
  it ← left_over,
  stx@(syntax.node ⟨ident, _⟩) ← token | error "" (dlist.singleton "identifier") it,
  pure stx
} <?> "identifier"

instance ident.parser.tokens : parser.has_tokens (ident.parser : parser) := default _
instance ident.parser.view : parser.has_view (ident.parser : parser) ident.view :=
{..ident.has_view}

def ident_part.view.to_string : ident_part.view → string
| (ident_part.view.default (some atom)) := atom.val
| (ident_part.view.escaped {escaped := some atom, ..}) := atom.val
| _ := "ident_part.view: invalid input"

def ident.view.components : ident.view → list string
| {part := part, suffix := none} := [part.to_string]
| {part := part, suffix := some suffix} := part.to_string :: (view ident suffix.ident).components

def ident.view.to_name (id : ident.view) : name :=
id.components.foldl name.mk_string name.anonymous

/-- Read identifier without consulting the token table. -/
def raw_ident.parser : parser :=
lift $ ident' >>= with_trailing

instance raw_ident.parser.tokens : parser.has_tokens (raw_ident.parser : parser) := default _
instance raw_ident.parser.view : parser.has_view (raw_ident.parser : parser) ident.view :=
{..ident.has_view}

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
    (match view ident stx with
     | {part := ident_part.view.default (some ⟨_, sym'⟩),
        suffix := none} := some sym'
     | _ := none)
  | _ := none,
  when (sym' ≠ some sym) $
    error "" (dlist.singleton (repr sym)) it,
  pure stx

instance symbol_or_ident.tokens (sym) : parser.has_tokens (symbol_or_ident sym : parser) :=
default _
instance symbol_or_ident.view (sym) : parser.has_view (symbol_or_ident sym : parser) syntax := default _

/-- A unicode symbol with an ASCII fallback -/
@[derive has_tokens has_view]
def unicode_symbol (unicode ascii : string) (lbp := 0) : parser :=
lift $ any_of [symbol unicode lbp, symbol ascii lbp]
-- use unicode variant by default
instance unicode_symbol.view_default (u a lbp) : parser.has_view_default (unicode_symbol u a lbp : parser) _ (syntax.atom ⟨none, u⟩) := ⟨⟩

end «parser»
end lean
