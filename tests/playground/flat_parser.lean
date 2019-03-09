import init.lean.message init.lean.parser.syntax init.lean.parser.trie init.lean.parser.basic

namespace lean
namespace flat_parser
open string
open parser (syntax syntax.missing)
open parser (trie token_map)

structure token_config :=
(«prefix» : string)
(lbp : nat := 0)

structure frontend_config :=
(filename : string)
(input    : string)
(file_map : file_map)

/- Remark: if we have a node in the trie with `some token_config`, the string induced by the path is equal to the `token_config.prefix`. -/
structure parser_config extends frontend_config :=
(tokens : trie token_config)

-- Backtrackable state
structure parser_state :=
(messages : message_log)

structure token_cache_entry :=
(start_it stop_it : string.iterator)
(tk : syntax)

-- Non-backtrackable state
structure parser_cache :=
(token_cache : option token_cache_entry := none)

inductive result (α : Type)
| ok       (a : α) (it : iterator) (cache : parser_cache) (state : parser_state) (eps : bool) : result
| error {} (it : iterator) (cache : parser_cache) (msg : string) (stx : syntax) (eps : bool) : result

inductive result.is_ok {α : Type} : result α → Prop
| mk (a : α) (it : iterator) (cache : parser_cache) (state : parser_state) (eps : bool) : result.is_ok (result.ok a it cache state eps)

theorem error_is_not_ok {α : Type} {it : iterator} {cache : parser_cache} {msg : string} {stx : syntax} {eps : bool}
                        (h : result.is_ok (@result.error α it cache msg stx eps)) : false :=
match h with end

@[inline] def unreachable_error {α β : Type} {it : iterator} {cache : parser_cache} {msg : string} {stx : syntax} {eps : bool}
                                (h : result.is_ok (@result.error α it cache msg stx eps)) : β :=
false.elim (error_is_not_ok h)

def result_ok := {r : result unit // r.is_ok}

@[inline] def mk_result_ok (it : iterator) (cache : parser_cache) (state : parser_state) : result_ok :=
⟨result.ok () it cache state tt, result.is_ok.mk _ _ _ _ _⟩

def parser_core_m (α : Type) :=
parser_config → result_ok → result α
abbreviation parser_core := parser_core_m syntax

structure rec_parsers :=
(cmd_parser  : parser_core)
(lvl_parser  : nat → parser_core)
(term_parser : nat → parser_core)

def parser_m (α : Type) := rec_parsers → parser_core_m α
abbreviation parser := parser_m syntax
abbreviation trailing_parser := syntax → parser

@[inline] def command.parser : parser := λ ps, ps.cmd_parser
@[inline] def level.parser (rbp : nat := 0) : parser := λ ps, ps.lvl_parser rbp
@[inline] def term.parser (rbp : nat := 0) : parser  := λ ps, ps.term_parser rbp

@[inline] def parser_m.pure {α : Type} (a : α) : parser_m α :=
λ _ _ r,
  match r with
  | ⟨result.ok _ it c s _, h⟩   := result.ok a it c s tt
  | ⟨result.error _ _ _ _ _, h⟩ := unreachable_error h

@[inline_if_reduce] def eager_or  (b₁ b₂ : bool) := b₁ || b₂
@[inline_if_reduce] def eager_and (b₁ b₂ : bool) := b₁ && b₂

@[inline] def parser_m.bind {α β : Type} (x : parser_m α) (f : α → parser_m β) : parser_m β :=
λ ps cfg r,
  match x ps cfg r with
  | result.ok a it c s e₁ :=
    (match f a ps cfg (mk_result_ok it c s) with
     | result.ok b it c s e₂        := result.ok b it c s (eager_and e₁ e₂)
     | result.error it c msg stx e₂ := result.error it c msg stx (eager_and e₁ e₂))
  | result.error it c msg stx e  := result.error it c msg stx e

instance : monad parser_m :=
{pure := @parser_m.pure, bind := @parser_m.bind}

@[inline] protected def orelse {α : Type} (p q : parser_m α) : parser_m α :=
λ ps cfg r,
  match r with
  | ⟨result.ok _ it₁ _ s₁ _, _⟩ :=
    (match p ps cfg r with
     | result.error it₂ c₂ msg₁ stx₁ tt := q ps cfg (mk_result_ok it₁ c₂ s₁)
     | other                            := other)
  | ⟨result.error _ _ _ _ _, h⟩ := unreachable_error h

@[inline] protected def failure {α : Type} : parser_m α :=
λ _ _ r,
  match r with
  | ⟨result.ok _ it c s _, h⟩   := result.error it c "failure" syntax.missing tt
  | ⟨result.error _ _ _ _ _, h⟩ := unreachable_error h

instance : alternative parser_m :=
{ orelse         := @flat_parser.orelse,
  failure        := @flat_parser.failure,
  ..flat_parser.monad }

def set_silent_error {α : Type} : result α → result α
| (result.error it c msg stx _) := result.error it c msg stx tt
| other                         := other

/--
`try p` behaves like `p`, but it pretends `p` hasn't
consumed any input when `p` fails.
-/
@[inline] def try {α : Type} (p : parser_m α) : parser_m α :=
λ ps cfg r, set_silent_error (p ps cfg r)

/-
private def str_aux (c : parser_cache) (s : parser_state) (str : string) : nat → iterator → iterator → result unit
| 0     _    it := result.ok () it c s (str.length ≠ 0)
| (n+1) s_it it :=
  if it.has_next && s_it.curr = it.curr then str_aux n s_it.next it.next
  else result.error

def str (s : string) : parser_m string :=
-/

def mk_error {α : Type} (r : result_ok) (msg : string) (stx : syntax := syntax.missing) : result α :=
match r with
| ⟨result.ok _ it c s _, _⟩   := result.error it c msg stx tt
| ⟨result.error _ _ _ _ _, h⟩ := unreachable_error h

def cmd_not_allowed : parser_core :=
λ cfg r, mk_error r "commands are not allowed here"

def term_not_allowed : nat → parser_core :=
λ rbp cfg r, mk_error r "terms are not allowed here"

def rec_lvl (parse_lvl : nat → parser) : nat → nat → parser_core
| 0     rbp cfg r := mk_error r "parser: no progress"
| (n+1) rbp cfg r := parse_lvl rbp ⟨cmd_not_allowed, rec_lvl n, term_not_allowed⟩ cfg r

mutual def rec_cmd, rec_term (parse_cmd : parser) (parse_term : nat → parser) (parse_lvl : nat → parser_core)
with rec_cmd  : nat → parser_core
| 0     cfg r := mk_error r "parser: no progress"
| (n+1) cfg r := parse_cmd ⟨rec_cmd n, parse_lvl, rec_term n⟩ cfg r
with rec_term : nat → nat → parser_core
| 0     rbp cfg r := mk_error r "parser: no progress"
| (n+1) rbp cfg r := parse_term rbp ⟨rec_cmd n, parse_lvl, rec_term n⟩ cfg r

def run_parser (x : parser) (parse_cmd : parser) (parse_lvl : nat → parser) (parse_term : nat → parser)
               (input : iterator) (cfg : parser_config) : result syntax :=
let it := input in
let n  := it.remaining in
let r  := mk_result_ok it {} {messages := message_log.empty} in
let pl := rec_lvl (parse_lvl) n in
let ps : rec_parsers := { cmd_parser  := rec_cmd parse_cmd parse_term pl n,
                          lvl_parser  := pl,
                          term_parser := rec_term parse_cmd parse_term pl n } in
x ps cfg r

structure parsing_tables :=
(leading_term_parsers : token_map parser)
(trailing_term_parsers : token_map trailing_parser)

abbreviation command_parser_m (α : Type) :=
parsing_tables → parser_m α

end flat_parser
end lean

def main : io uint32 :=
io.println' "ok" *>
pure 0
