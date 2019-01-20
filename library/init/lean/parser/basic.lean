/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Parser for the Lean language
-/
prelude
import init.lean.parser.parsec init.lean.parser.syntax init.lean.parser.rec
import init.lean.parser.trie
import init.lean.parser.identifier init.data.rbmap init.lean.message
import init.control.coroutine

namespace lean
namespace parser

/- Maximum standard precedence. This is the precedence of function application.
   In the standard Lean language, only the token `.` has a left-binding power greater
   than `max_prec` (so that field accesses like `g (h x).f` are parsed as `g ((h x).f)`,
   not `(g (h x)).f`). -/
def max_prec : nat := 1024

structure token_config :=
(«prefix» : string)
/- Left-binding power used by the term parser. The term parser operates in the context
   of a right-binding power between 0 (used by parentheses and on the top-level) and
   (usually) `max_prec` (used by function application). After parsing an initial term,
   it continues parsing and expanding that term only when the left-binding power of
   the next token is greater than the current right-binding power. For example, it
   never continues parsing an argument after the initial parse, unless a token with
   lbp > max_prec is encountered. Conversely, the term parser will always continue
   parsing inside parentheses until it finds a token with lbp 0 (such as `)`). -/
(lbp : nat := 0)
-- reading a token should not need any state
/- An optional parser that is activated after matching `prefix`.
   It should return a syntax tree with a "hole" for the
   `source_info` surrounding the token, which will be supplied
   by the `token` parser.

   Remark: `suffix_parser` has many applications for example for parsing
   hexdecimal numbers, `prefix` is `0x` and `suffix_parser` is the parser `digit*`.
   We also use it to parse string literals: here `prefix` is just `"`.
-/
(suffix_parser : option (parsec' (source_info → syntax)) := none)

-- Backtrackable state
structure parser_state :=
(messages : message_log)

structure token_cache_entry :=
(start_it stop_it : string.iterator)
(tk : syntax)

-- Non-backtrackable state
structure parser_cache :=
(token_cache : option token_cache_entry := none)
-- for profiling
(hit miss : nat := 0)

structure frontend_config :=
(filename : string)
(input    : string)
(file_map : file_map := file_map.from_string input)

/- Remark: if we have a node in the trie with `some token_config`, the string induced by the path is equal to the `token_config.prefix`. -/
structure parser_config extends frontend_config :=
(tokens : trie token_config)

instance parser_config_coe : has_coe parser_config frontend_config :=
⟨parser_config.to_frontend_config⟩

@[derive monad alternative monad_parsec monad_except]
def parser_core_t (m : Type → Type) [monad m] :=
parsec_t syntax $ state_t parser_cache $ m

@[derive monad alternative monad_reader monad_parsec monad_except]
def parser_t (ρ : Type) (m : Type → Type) [monad m] := reader_t ρ $ parser_core_t m
@[derive monad alternative monad_reader monad_parsec monad_except]
def basic_parser_m := parser_t parser_config id
abbreviation basic_parser := basic_parser_m syntax
abbreviation monad_basic_parser := has_monad_lift_t basic_parser_m

section
local attribute [reducible] basic_parser_m parser_t parser_core_t
@[inline] def get_cache : basic_parser_m parser_cache :=
monad_lift (get : state_t parser_cache id _)

@[inline] def put_cache : parser_cache → basic_parser_m punit :=
λ c, monad_lift (put c : state_t parser_cache id _)
end

 -- an arbitrary `parser` type; parsers are usually some monad stack based on `basic_parser_m` returning `syntax`
variable {ρ : Type}

class has_tokens (r : ρ) := mk {} ::
(tokens : list token_config)

@[noinline, nospecialize] def tokens (r : ρ) [has_tokens r] :=
has_tokens.tokens r

instance has_tokens.inhabited (r : ρ) : inhabited (has_tokens r) :=
⟨⟨[]⟩⟩

instance list.nil.tokens : parser.has_tokens ([] : list ρ) :=
default _

instance list.cons.tokens (r : ρ) (rs : list ρ) [parser.has_tokens r] [parser.has_tokens rs] :
  parser.has_tokens (r::rs) :=
⟨tokens r ++ tokens rs⟩

class has_view (α : out_param Type) (r : ρ) :=
(view : syntax → α)
(review : α → syntax)

export has_view (view review)

def try_view {α : Type} (k : syntax_node_kind) [has_view α k] (stx : syntax) : option α :=
if stx.is_of_kind k then some (has_view.view k stx) else none

instance has_view.default (r : ρ) : inhabited (parser.has_view syntax r) :=
⟨{ view := id, review := id }⟩

class has_view_default (r : ρ) (α : out_param Type) [has_view α r] (default : α) := mk {}

def message_of_parsec_message {μ : Type} (cfg : frontend_config) (msg : parsec.message μ) : message :=
{filename := cfg.filename, pos := cfg.file_map.to_position msg.it.offset, text := msg.text}

/-- Run parser stack, returning a partial syntax tree in case of a fatal error -/
protected def run {m : Type → Type} {α ρ : Type} [monad m] [has_coe_t ρ frontend_config] (cfg : ρ) (s : string) (r : state_t parser_state (parser_t ρ m) α) :
m (sum α syntax × message_log) :=
do (r, _) ← (((r.run {messages:=message_log.empty}).run cfg).parse s).run {},
pure $ match r with
| except.ok (a, st) := (sum.inl a, st.messages)
| except.error msg  := (sum.inr msg.custom.get, message_log.empty.add (message_of_parsec_message cfg msg))

open coroutine
open monad_parsec
open parser.has_view
variables {α : Type} {m : Type → Type}
local notation `parser` := m syntax

def log_message {μ : Type} [monad m] [monad_reader ρ m] [has_lift_t ρ frontend_config] [monad_state parser_state m]
  (msg : parsec.message μ) : m unit :=
do cfg ← read,
   modify (λ st, {st with messages := st.messages.add (message_of_parsec_message ↑cfg msg)})

def mk_token_trie (tokens : list token_config) : except string (trie token_config) :=
do -- the only hardcoded tokens, because they are never directly mentioned by a `parser`
   let builtin_tokens : list token_config := [{«prefix» := "/-"}, {«prefix» := "--"}],
   t ← (builtin_tokens ++ tokens).mfoldl (λ (t : trie token_config) tk,
     match t.find tk.prefix with
     | some tk' := (match tk.lbp, tk'.lbp with
       | l, 0  := pure $ t.insert tk.prefix tk
       | 0, _  := pure t
       | l, l' := if l = l' then pure t else throw $
         "invalid token '" ++ tk.prefix ++ "', has been defined with precedences " ++
         to_string l ++ " and " ++ to_string l')
     | none := pure $ t.insert tk.prefix tk)
     trie.mk,
   pure t


/- Monad stacks used in multiple files -/

/- NOTE: We move `rec_t` under `parser_t`'s `reader_t` so that `term_parser`, which does not
   have access to `command_parser`'s ρ (=`command_parser_config`) can still recurse into it
   (for command quotations). This means that the `command_parser_config` will be reset
   on a recursive call to `command.parser`, i.e. it forgets about locally registered parsers,
   but that's not an issue for our intended uses of it. -/
@[derive monad alternative monad_reader monad_parsec monad_except monad_rec]
def command_parser_m (ρ : Type) := reader_t ρ $ rec_t unit syntax $ parser_core_t id

section
local attribute [reducible] parser_t command_parser_m
instance command_parser_m.monad_reader_adapter (ρ ρ' : Type) :
  monad_reader_adapter ρ ρ' (command_parser_m ρ) (command_parser_m ρ') :=
infer_instance
instance command_parser_m.basic_parser (ρ : Type) [has_lift_t ρ parser_config] : monad_basic_parser (command_parser_m ρ) :=
⟨λ _ x cfg rec, x.run ↑cfg⟩
end

/- The `nat` at `rec_t` is the lbp` -/
@[derive monad alternative monad_reader monad_parsec monad_except monad_rec monad_basic_parser]
def term_parser_m := rec_t nat syntax $ command_parser_m parser_config
abbreviation term_parser := term_parser_m syntax

/-- A term parser for a suffix or infix notation that accepts a preceding term. -/
@[derive monad alternative monad_reader monad_parsec monad_except monad_rec monad_basic_parser]
def trailing_term_parser_m := reader_t syntax term_parser_m
abbreviation trailing_term_parser := trailing_term_parser_m syntax

instance trailing_term_parser_coe : has_coe term_parser trailing_term_parser :=
⟨λ x _, x⟩

local attribute [instance] name.has_lt_quick
/-- A multimap indexed by tokens. Used for indexing parsers by their leading token. -/
def token_map (α : Type) := rbmap name (list α) (<)

def token_map.insert {α : Type} (map : token_map α) (k : name) (v : α) : token_map α :=
match map.find k with
| none    := map.insert k [v]
| some vs := map.insert k (v::vs)

def token_map.of_list {α : Type} : list (name × α) → token_map α
| []          := mk_rbmap _ _ _
| (⟨k,v⟩::xs) := (token_map.of_list xs).insert k v

instance token_map_nil.tokens : parser.has_tokens $ @token_map.of_list ρ [] :=
default _

instance token_map_cons.tokens (k : name) (r : ρ) (rs : list (name × ρ)) [parser.has_tokens r] [parser.has_tokens $ token_map.of_list rs] :
  parser.has_tokens $ token_map.of_list ((k,r)::rs) :=
⟨tokens r ++ tokens (token_map.of_list rs)⟩

-- This needs to be a separate structure since `term_parser`s cannot contain themselves in their config
structure command_parser_config extends parser_config :=
(leading_term_parsers : token_map term_parser)
(trailing_term_parsers : token_map trailing_term_parser)
-- local term parsers (such as from `local notation`) hide previous parsers instead of overloading them
(local_leading_term_parsers : token_map term_parser := mk_rbmap _ _ _)
(local_trailing_term_parsers : token_map trailing_term_parser := mk_rbmap _ _ _)

instance command_parser_config_coe_parser_config : has_coe command_parser_config parser_config :=
⟨command_parser_config.to_parser_config⟩

abbreviation command_parser := command_parser_m command_parser_config syntax

end «parser»
end lean
