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
import init.lean.parser.combinators init.lean.parser.string_literal

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
  str "-/" *> (if nesting = 1 then pure () else finish_comment_block_aux (nesting - 1) n)
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

variables [monad_basic_parser m]

private mutual def update_trailing, update_trailing_lst
with update_trailing : substring → syntax → syntax
| trailing (syntax.atom a@⟨some info, _⟩) := syntax.atom {a with info := some {info with trailing := trailing}}
| trailing (syntax.raw_node n) := syntax.raw_node {n with args := update_trailing_lst trailing n.args}
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
instance raw.view {α} (p : m α) (t) : parser.has_view (option syntax_atom) (raw p t : parser) :=
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

--TODO(Sebastian): other bases
def number' : basic_parser :=
node_choice! number {
  base10: raw (take_while1 char.is_digit),
}

def string_lit' : basic_parser :=
node! string_lit [val: raw parse_string_literal]

private def mk_consume_token (tk : token_config) (it : string.iterator) : basic_parser :=
let it' := it.nextn tk.prefix.length in
monad_parsec.lift $ λ _, parsec.result.ok (mk_raw_res it it') it' none

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
     put_cache {cache with hit := cache.hit + 1},
     pure tkc.tk
   ) (λ _, do
     -- cache failed, update cache

     ident_start ← observing $ lookahead (satisfy is_id_first <|> ch id_begin_escape),
     tk ← match_token,
     tk ← match tk, ident_start with
     | some tk@{suffix_parser := some _, ..}, _ :=
       error "token: not implemented" --str tk *> monad_parsec.lift r
     | some tk, except.ok _ := do
       id ← ident',
       it' ← left_over,
       -- if a token is both a symbol and a valid identifier (i.e. a keyword),
       -- we want it to be recognized as a symbol
       if it.offset + tk.prefix.length ≥ it'.offset then
         mk_consume_token tk it
       else pure id
     | some tk, except.error _ := mk_consume_token tk it
     | none, except.ok _ := ident'
     | none, except.error _ := number' <|> string_lit',
     tk ← with_trailing tk,
     new_it ← left_over,
     put_cache {cache with token_cache := some ⟨it, new_it, tk⟩, miss := cache.miss + 1},
     pure tk
   )

def peek_token : basic_parser_m (except (parsec.message syntax) syntax) :=
do st ← get,
   observing (try (lookahead token)) <* put st

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
instance symbol.view (sym lbp) : parser.has_view (option syntax_atom) (symbol sym lbp : parser) :=
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
instance number.parser.view : parser.has_view number.view (number.parser : parser) :=
{..number.has_view}

def number.view.to_nat : number.view → nat
| (number.view.base10 (some atom)) := atom.val.to_nat
| _ := 1138 -- should never happen, but let's still choose a grep-able number

def number.view.of_nat (n : nat) : number.view :=
number.view.base10 (some {val := to_string n})

def string_lit.parser : parser :=
lift $ try $ do {
  it ← left_over,
  stx ← token,
  some _ ← pure $ try_view string_lit stx | error "" (dlist.singleton "number") it,
  pure stx
} <?> "string"

instance string_lit.parser.tokens : parser.has_tokens (string_lit.parser : parser) := default _
instance string_lit.parser.view : parser.has_view string_lit.view (string_lit.parser : parser) :=
{..string_lit.has_view}

def ident.parser : parser :=
lift $ try $ do {
  it ← left_over,
  stx ← token,
  if stx.is_of_kind ident then pure stx
  else error "" (dlist.singleton "identifier") it
} <?> "identifier"

instance ident.parser.tokens : parser.has_tokens (ident.parser : parser) := default _
instance ident.parser.view : parser.has_view ident.view (ident.parser : parser) :=
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
instance raw_ident.parser.view : parser.has_view ident.view (raw_ident.parser : parser) :=
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
  | syntax.raw_node {kind := @ident, ..} :=
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
instance symbol_or_ident.view (sym) : parser.has_view syntax (symbol_or_ident sym : parser) := default _

/-- A unicode symbol with an ASCII fallback -/
@[derive has_tokens has_view]
def unicode_symbol (unicode ascii : string) (lbp := 0) : parser :=
lift $ any_of [symbol unicode lbp, symbol ascii lbp]
-- use unicode variant by default
instance unicode_symbol.view_default (u a lbp) : parser.has_view_default (unicode_symbol u a lbp : parser) _ (syntax.atom ⟨none, u⟩) := ⟨⟩

def indexed {α : Type} (map : token_map α) : m (list α) :=
lift $ do
  except.ok tk ← peek_token | error "",
  n ← match tk with
  | syntax.atom ⟨_, s⟩ := pure $ mk_simple_name s
  | syntax.raw_node n := pure n.kind.name
  | _ := error "",
  option.to_monad $ map.find n

namespace syntax
open lean.format

-- Now that we have `ident.view`, this function is much easier to define
protected mutual def to_format, to_format_lst
with to_format : syntax → format
| (atom ⟨_, s⟩) := to_fmt $ repr s
| stx@(raw_node n) :=
  let scopes := match n.scopes with [] := to_fmt "" | _ := bracket "{" (join_sep n.scopes ", ") "}" in
  if n.kind.name = `lean.parser.no_kind then sbracket $ scopes ++ join_sep (to_format_lst n.args) line
  else if n.kind.name = `lean.parser.ident then
    to_fmt "`" ++ to_fmt (view ident stx).to_name ++ scopes
  else let shorter_name := n.kind.name.replace_prefix `lean.parser name.anonymous
       in paren $ join_sep ((to_fmt shorter_name ++ scopes) :: to_format_lst n.args) line
| missing := "<missing>"
with to_format_lst : list syntax → list format
| []      := []
| (s::ss) := to_format s :: to_format_lst ss

instance : has_to_format syntax := ⟨syntax.to_format⟩
instance : has_to_string syntax := ⟨to_string ∘ to_fmt⟩

end syntax
end «parser»
end lean
