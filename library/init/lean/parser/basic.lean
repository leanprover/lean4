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
   by the `token` parser. -/
(token_parser : option (parsec' (source_info → syntax)) := none)

structure parser_state :=
(tokens : trie token_config)
(messages : message_log)

structure parser_config :=
(filename : string)

@[derive monad alternative monad_reader monad_state monad_parsec monad_except]
def parser_t (m : Type → Type) [monad m] := reader_t parser_config $ state_t parser_state $ parsec_t syntax m
abbreviation basic_parser_m := parser_t id
abbreviation basic_parser := basic_parser_m syntax
abbreviation monad_basic_read := has_monad_lift_t basic_parser_m

 -- an arbitrary `parser` type; parsers are usually some monad stack based on `basic_parser_m` returning `syntax`
variable {ρ : Type}

class has_tokens (r : ρ) := mk {} ::
(tokens : list token_config)

open parser.has_tokens (tokens)

instance list.nil.tokens : parser.has_tokens ([] : list ρ) :=
⟨[]⟩
instance list.cons.tokens (r : ρ) (rs : list ρ) [parser.has_tokens r] [parser.has_tokens rs] :
  parser.has_tokens (r::rs) :=
⟨tokens r ++ tokens rs⟩

protected class has_view (r : ρ) (α : out_param Type) :=
(view : syntax → option α)
(review : α → syntax)

instance has_view.default (r : ρ) : inhabited (parser.has_view r syntax) :=
⟨{ view := some, review := id }⟩

class syntax_node_kind.has_view (k : syntax_node_kind) (α : out_param Type) :=
(view : syntax → option α)
(review : α → syntax)

def message_of_parsec_message {μ : Type} (cfg : parser_config) (msg : parsec.message μ) : message :=
-- FIXME: translate position
{filename := cfg.filename, pos := ⟨0, 0⟩, text := to_string msg}

section
local attribute [reducible] parser_t
protected def run {m : Type → Type} [monad m] (cfg : parser_config) (st : parser_state) (s : string) (r : parser_t m syntax) :
m (syntax × message_log) :=
do r ← ((r.run cfg).run st).parse_with_eoi s,
pure $ match r with
| except.ok (stx, st) := (stx.update_leading s, st.messages)
| except.error msg  := (msg.custom.update_leading s, message_log.empty.add (message_of_parsec_message cfg msg))
end

open monad_parsec
open parser.has_view
variables {α : Type} {m : Type → Type}
local notation `parser` := m syntax

def log_message {μ : Type} [monad m] [monad_reader parser_config m] [monad_state parser_state m] (msg : parsec.message μ) : m unit :=
do cfg ← read,
   modify (λ st, {st with messages := st.messages.add (message_of_parsec_message cfg msg)})

def eoi : syntax_node_kind := ⟨`lean.parser.eoi⟩

protected def parse [monad m] (cfg : parser_config) (s : string) (r : parser_t m syntax) [parser.has_tokens r] :
  m (syntax × message_log) :=
-- the only hardcoded tokens, because they are never directly mentioned by a `parser`
let builtin_tokens : list token_config := [⟨"/-", 0, none⟩, ⟨"--", 0, none⟩] in
let trie := (tokens r ++ builtin_tokens).foldl (λ t cfg, trie.insert t cfg.prefix cfg) trie.mk in
parser.run cfg ⟨trie, message_log.empty⟩ s $ do
  stx ← catch r $ λ (msg : parsec.message _), do {
    parser.log_message msg,
    pure msg.custom
  },
  -- add `eoi` node
  catch monad_parsec.eoi parser.log_message,
  let stop := s.mk_iterator.to_end,
  pure $ syntax.node ⟨none, [
    stx,
    syntax.node ⟨eoi, [syntax.atom ⟨some ⟨⟨stop, stop⟩, stop.offset, ⟨stop, stop⟩⟩, ""⟩]⟩
  ]⟩

structure parse.view_ty :=
(root : syntax)
(eoi  : syntax)

def parse.view : syntax → option parse.view_ty
| (syntax.node ⟨none, [root, eoi]⟩) := some ⟨root, eoi⟩
| _ := none


/- Monad stacks used in multiple files -/

@[derive monad alternative monad_reader monad_state monad_parsec monad_except monad_rec monad_basic_read]
def command_parser_m := rec_t unit syntax basic_parser_m
abbreviation command_parser := command_parser_m syntax

@[derive monad alternative monad_reader monad_state monad_parsec monad_except monad_rec monad_basic_read]
def term_parser_m := rec_t nat syntax command_parser_m
abbreviation term_parser := term_parser_m syntax

end «parser»
end lean
