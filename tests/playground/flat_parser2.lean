import init.lean.message init.lean.parser.syntax init.lean.parser.trie init.lean.parser.basic
import init.lean.parser.token

namespace lean
namespace flat_parser
open string
open parser (syntax syntax.missing syntax.atom syntax.ident syntax.raw_node number string_lit)
open parser (trie token_map)
def max_prec : nat := 1024

abbrev pos := string.utf8_pos

/-- A precomputed cache for quickly mapping char offsets to positions. -/
structure file_map :=
(offsets : array nat)
(lines   : array nat)

namespace file_map
private def from_string_aux (s : string) : nat → nat → nat → pos → array nat → array nat → file_map
| 0     offset line i offsets lines := ⟨offsets.push offset, lines.push line⟩
| (k+1) offset line i offsets lines :=
  if s.utf8_at_end i then ⟨offsets.push offset, lines.push line⟩
  else let c := s.utf8_get i in
       let i := s.utf8_next i in
       let offset := offset + 1 in
       if c = '\n'
       then from_string_aux k offset (line+1) i (offsets.push offset) (lines.push (line+1))
       else from_string_aux k offset line i offsets lines

def from_string (s : string) : file_map :=
from_string_aux s s.length 0 1 0 (array.nil.push 0) (array.nil.push 1)

/- Remark: `offset is in [(offsets.get b), (offsets.get e)]` and `b < e` -/
private def to_position_aux (offsets : array nat) (lines : array nat) (offset : nat) : nat → nat → nat → position
| 0     b e := ⟨offset, 1⟩ -- unreachable
| (k+1) b e :=
  let offset_b := offsets.read' b in
  if e = b + 1 then ⟨offset - offset_b, lines.read' b⟩
  else let m := (b + e) / 2 in
       let offset_m := offsets.read' m in
       if offset = offset_m then ⟨0, lines.read' m⟩
       else if offset > offset_m then to_position_aux k m e
       else to_position_aux k b m

def to_position : file_map → nat → position
| ⟨offsets, lines⟩ offset := to_position_aux offsets lines offset offsets.size 0 (offsets.size-1)
end file_map

structure token_config :=
(«prefix» : string)
(lbp : nat := 0)

structure frontend_config :=
(filename : string)
(input    : string)
(file_map : file_map)

/- Remark: if we have a node in the trie with `some token_config`, the string induced by the path is equal to the `token_config.prefix`. -/
structure parser_config extends frontend_config :=
(tokens      : trie token_config)

-- Backtrackable state
structure parser_state :=
(messages : message_log)

structure token_cache_entry :=
(start_pos stop_pos : pos)
(tk : syntax)

-- Non-backtrackable state
structure parser_cache :=
(token_cache : option token_cache_entry := none)

inductive result (α : Type)
| ok       (a : α)        (i : pos) (cache : parser_cache) (state : parser_state) (eps : bool) : result
| error {} (msg : string) (i : pos) (cache : parser_cache) (stx : syntax)         (eps : bool) : result

inductive result.is_ok {α : Type} : result α → Prop
| mk (a : α) (i : pos) (cache : parser_cache) (state : parser_state) (eps : bool) : result.is_ok (result.ok a i cache state eps)

theorem error_is_not_ok {α : Type} {msg : string} {i : pos} {cache : parser_cache} {stx : syntax} {eps : bool}
                        (h : result.is_ok (@result.error α msg i cache stx eps)) : false :=
match h with end

@[inline] def unreachable_error {α β : Type} {msg : string} {i : pos} {cache : parser_cache} {stx : syntax} {eps : bool}
                                (h : result.is_ok (@result.error α msg i cache stx eps)) : β :=
false.elim (error_is_not_ok h)

def result_ok := {r : result unit // r.is_ok}

@[inline] def mk_result_ok (i : pos) (cache : parser_cache) (state : parser_state) (eps := tt) : result_ok :=
⟨result.ok () i cache state eps, result.is_ok.mk _ _ _ _ _⟩

def mk_error {α : Type} (r : result_ok) (msg : string) (stx : syntax := syntax.missing) (eps := tt) : result α :=
match r with
| ⟨result.ok _ i c s _, _⟩    := result.error msg i c stx eps
| ⟨result.error _ _ _ _ _, h⟩ := unreachable_error h

def parser_core_m (α : Type) :=
result_ok → result α
abbrev parser_core := parser_core_m syntax

@[inline] def parser_core_m.pure {α : Type} (a : α) : parser_core_m α :=
λ r,
  match r with
  | ⟨result.ok _ it c s _, h⟩   := result.ok a it c s tt
  | ⟨result.error _ _ _ _ _, h⟩ := unreachable_error h

@[inline_if_reduce] def strict_or  (b₁ b₂ : bool) := b₁ || b₂
@[inline_if_reduce] def strict_and (b₁ b₂ : bool) := b₁ && b₂

@[inline] def parser_core_m.bind {α β : Type} (x : parser_core_m α) (f : α → parser_core_m β) : parser_core_m β :=
λ r,
  match x r with
  | result.ok a i c s e₁ :=
    (match f a (mk_result_ok i c s) with
     | result.ok b i c s e₂        := result.ok b i c s (strict_and e₁ e₂)
     | result.error msg i c stx e₂ := result.error msg i c stx (strict_and e₁ e₂))
  | result.error msg i c stx e  := result.error msg i c stx e

instance : monad parser_core_m :=
{bind := @parser_core_m.bind, pure := @parser_core_m.pure}

instance : inhabited parser_core :=
⟨λ r, mk_error r "error"⟩

@[inline] def parser_core_m.error {α : Type} (msg : string) : parser_core_m α :=
λ r, mk_error r msg

@[inline] def error {α : Type} {m : Type → Type} [has_monad_lift_t parser_core_m m] (msg : string) : m α :=
monad_lift $ parser_core_m.error msg

abbrev basic_parser_m : Type → Type              := reader_t parser_config parser_core_m
abbrev basic_parser : Type                       := basic_parser_m syntax
abbrev command_parser_m (ρ : Type) : Type → Type := reader_t ρ (reader_t parser_core parser_core_m)
abbrev term_parser_m : Type → Type               := reader_t (nat → parser_core) (command_parser_m parser_config)
abbrev term_parser : Type                        := term_parser_m syntax
abbrev trailing_term_parser : Type               := syntax → term_parser

structure command_parser_config extends parser_config :=
(leading_term_parsers  : token_map term_parser)
(trailing_term_parsers : token_map trailing_term_parser)

abbrev command_parser : Type      := command_parser_m command_parser_config syntax
abbrev command_parser_core : Type := command_parser_m parser_config syntax

@[inline] def term_parser_of_basic_parser {α : Type} (p : basic_parser_m α) : term_parser_m α :=
λ _ cfg _, p cfg

@[inline] def command_parser_of_basic_parser {α : Type} (p : basic_parser_m α) : command_parser_m command_parser_config α :=
λ cfg _, p cfg.to_parser_config

instance basic2term_p    : has_monad_lift basic_parser_m term_parser_m                            := ⟨@term_parser_of_basic_parser⟩
instance basic2command_p : has_monad_lift basic_parser_m (command_parser_m command_parser_config) := ⟨@command_parser_of_basic_parser⟩

@[inline] def term.parser (rbp := 0) : term_parser := λ p _ _, p rbp
@[inline] def command.parser : command_parser      := λ _ p, p

@[inline] def read_cfg : term_parser_m parser_config :=
λ _ cfg _, pure cfg

def peek_token : basic_parser_m syntax :=
error "TODO"

def curr_lbp : term_parser_m nat :=
do tk ← monad_lift peek_token,
   match tk with
   | syntax.atom ⟨_, sym⟩ := do
     cfg ← read_cfg,
     (match cfg.tokens.match_prefix sym.mk_iterator with
      | some ⟨_, tk_cfg⟩ := pure tk_cfg.lbp
      | _                := error "curr_lbp: unreachable")
   | syntax.raw_node {kind := @number, ..}     := pure max_prec
   | syntax.raw_node {kind := @string_lit, ..} := pure max_prec
   | syntax.ident _                            := pure max_prec
   | _                                         := error "curr_lbp: unknown token kind"



#exit

   match tk with
   | syntax.atom ⟨_, sym⟩ := do
     cfg ← read,
     -- some ⟨_, tk_cfg⟩ ← pure (cfg.tokens.match_prefix sym.mk_iterator) | error "curr_lbp: unreachable",
     pure 0
   | syntax.ident _ := pure max_prec
   | syntax.raw_node {kind := @number, ..} := pure max_prec
   | syntax.raw_node {kind := @string_lit, ..} := pure max_prec
   | _ := error "curr_lbp: unknown token kind"





private def trailing (cfg : command_parser_config) : trailing_term_parser :=
λ _ p _ _ r, p 0 r -- TODO(Leo)

private def leading (cfg : command_parser_config) : term_parser :=
λ p _ _ r, p 0 r -- TODO(Leo)

def dummy : nat → parser_core :=
λ _ r, mk_error r "dummy"

def pratt (leading_p : term_parser) (trailing_p : trailing_term_parser) (p : term_parser) : command_parser_core :=
p dummy

def command_parser_of_term_parser (p : term_parser) : command_parser :=
λ cfg rec r,
  let leading_p  : term_parser          := leading cfg in
  let trailing_p : trailing_term_parser := trailing cfg in
  let cfg        : parser_config        := cfg.to_parser_config in
  let p          : command_parser_core  := pratt leading_p trailing_p p in
  p cfg rec r

#exit

def pratt_parser (cfg : command_parser_config) : term_parser :=
leading



@[inline] def to_parser_core (term_p : nat → parser) (cmd_p : parser_core) : nat → parser_core :=
fix (λ rec_f rbp cfg r, term_p rbp cmd_p rec_f cfg r)

@[inline] def parser.run (x : parser) (term_p : nat → parser) (cmd_p : parser_core) : parser_core :=
x cmd_p (to_parser_core term_p cmd_p)




-- STOPPED HERE
#exit

def parser_core.run (cmd_p : parser_core) (term_p : parser_core) : parser_core :=



def aux (f : nat → parser_core) : nat → parser_core

structure command_parser_config extends rec_parser_config :=
(leading_term_parsers  : token_map parser)
(trailing_term_parsers : token_map trailing_parser)

abbrev command_parser_m (α : Type) : Type := parser_core_m command_parser_config α
abbrev command_parser := command_parser_m syntax





#exit
-- abbrev


-- def parser_m (α : Type) := rec_parsers → parser_core_m α
abbreviation parser := parser_m syntax
abbreviation trailing_parser := syntax → parser

@[inline] def command.parser : parser := λ cfg, cfg.cmd_parser cfg

@[inline] def term.parser (rbp : nat := 0) : parser  := λ ps, ps.term_parser rbp


instance : monad parser_m :=
{pure := @parser_m.pure, bind := @parser_m.bind}

@[inline] protected def orelse {α : Type} (p q : parser_m α) : parser_m α :=
λ ps cfg r,
  match r with
  | ⟨result.ok _ i₁ _ s₁ _, _⟩ :=
    (match p ps cfg r with
     | result.error msg₁ i₂ c₂ stx₁ tt := q ps cfg (mk_result_ok i₁ c₂ s₁)
     | other                           := other)
  | ⟨result.error _ _ _ _ _, h⟩ := unreachable_error h

@[inline] protected def failure {α : Type} : parser_m α :=
λ _ _ r,
  match r with
  | ⟨result.ok _ i c s _, h⟩    := result.error "failure" i c syntax.missing tt
  | ⟨result.error _ _ _ _ _, h⟩ := unreachable_error h

instance : alternative parser_m :=
{ orelse         := @flat_parser.orelse,
  failure        := @flat_parser.failure,
  ..flat_parser.monad }

def set_silent_error {α : Type} : result α → result α
| (result.error i c msg stx _) := result.error i c msg stx tt
| other                        := other

/--
`try p` behaves like `p`, but it pretends `p` hasn't
consumed any input when `p` fails.
-/
@[inline] def try {α : Type} (p : parser_m α) : parser_m α :=
λ ps cfg r, set_silent_error (p ps cfg r)

@[inline] def at_end (cfg : parser_config) (i : pos) : bool :=
cfg.input.utf8_at_end i

@[inline] def curr (cfg : parser_config) (i : pos) : char :=
cfg.input.utf8_get i

@[inline] def next (cfg : parser_config) (i : pos) : pos :=
cfg.input.utf8_next i

@[inline] def input_size (cfg : parser_config) : nat :=
cfg.input.length

@[inline] def curr_pos : result_ok → pos
| ⟨result.ok _ i _ _ _, _⟩    := i
| ⟨result.error _ _ _ _ _, h⟩ := unreachable_error h

@[inline] def curr_state : result_ok → parser_state
| ⟨result.ok _ _ _ s _, _⟩    := s
| ⟨result.error _ _ _ _ _, h⟩ := unreachable_error h

@[inline] def satisfy (p : char → bool) : parser_m char :=
λ _ cfg r,
  match r with
  | ⟨result.ok _ i ch st e, _⟩ :=
    if at_end cfg i then mk_error r "end of input"
    else let c := curr cfg i in
         if p c then result.ok c (next cfg i) ch st ff
         else mk_error r "unexpected character"
  | ⟨result.error _ _ _ _ _, h⟩ := unreachable_error h

def any : parser_m char :=
satisfy (λ _, tt)

@[specialize] def take_until_aux (p : char → bool) (cfg : parser_config) : nat → result_ok → result unit
| 0     r := r.val
| (n+1) r :=
  match r with
  | ⟨result.ok _ i ch st e, _⟩ :=
    if at_end cfg i then r.val
    else let c := curr cfg i in
         if p c then r.val
         else take_until_aux n (mk_result_ok (next cfg i) ch st tt)
  | ⟨result.error _ _ _ _ _, h⟩ := unreachable_error h

@[specialize] def take_until (p : char → bool) : parser_m unit :=
λ ps cfg r, take_until_aux p cfg (input_size cfg) r

def take_until_new_line : parser_m unit :=
take_until (= '\n')

def whitespace : parser_m unit :=
take_until (λ c, !c.is_whitespace)

-- set_option trace.compiler.boxed true
--- set_option pp.implicit true

def str_aux (cfg : parser_config) (str : string) (error : string) : nat → result_ok → pos → result unit
| 0     r j := mk_error r error
| (n+1) r j :=
  if str.utf8_at_end j then r.val
  else
    match r with
    | ⟨result.ok _ i ch st e, _⟩ :=
      if at_end cfg i then result.error error i ch syntax.missing tt
      else if curr cfg i = str.utf8_get j then str_aux n (mk_result_ok (next cfg i) ch st tt) (str.utf8_next j)
      else result.error error i ch syntax.missing tt
    | ⟨result.error _ _ _ _ _, h⟩ := unreachable_error h

-- #exit

@[inline] def str (s : string) : parser_m unit :=
λ ps cfg r, str_aux cfg s ("expected " ++ repr s) (input_size cfg) r 0

@[specialize] def many_aux (p : parser_m unit) : nat → bool → parser_m unit
| 0     fst := pure ()
| (k+1) fst := λ ps cfg r,
  let i₀ := curr_pos r in
  let s₀ := curr_state r in
  match p ps cfg r with
  | result.ok a i c s _    := many_aux k ff ps cfg (mk_result_ok i c s)
  | result.error _ _ c _ _ := result.ok () i₀ c s₀ fst

@[inline] def many (p : parser_m unit) : parser_m unit  :=
λ ps cfg r, many_aux p (input_size cfg) tt ps cfg r

@[inline] def many1 (p : parser_m unit) : parser_m unit  :=
p *> many p

def dummy_parser_core : parser_core :=
λ cfg r, mk_error r "dummy"

def test_parser {α : Type} (x : parser_m α) (input : string) : string :=
let r :=
  x { cmd_parser := dummy_parser_core, term_parser := λ _, dummy_parser_core }
    { filename := "test", input := input, file_map := file_map.from_string input, tokens := lean.parser.trie.mk }
    (mk_result_ok 0 {} {messages := message_log.empty}) in
match r with
| result.ok _ i _ _ _      := "Ok at " ++ to_string i
| result.error msg i _ _ _ := "Error at " ++ to_string i ++ ": " ++ msg

/-
mutual def rec_cmd, rec_term (parse_cmd : parser) (parse_term : nat → parser) (parse_lvl : nat → parser_core)
with rec_cmd  : nat → parser_core
| 0     cfg r := mk_error r "parser: no progress"
| (n+1) cfg r := parse_cmd ⟨rec_cmd n, parse_lvl, rec_term n⟩ cfg r
with rec_term : nat → nat → parser_core
| 0     rbp cfg r := mk_error r "parser: no progress"
| (n+1) rbp cfg r := parse_term rbp ⟨rec_cmd n, parse_lvl, rec_term n⟩ cfg r
-/

/-
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
-/

structure parsing_tables :=
(leading_term_parsers : token_map parser)
(trailing_term_parsers : token_map trailing_parser)

abbreviation command_parser_m (α : Type) :=
parsing_tables → parser_m α

end flat_parser
end lean

def mk_big_string : nat → string → string
| 0     s := s
| (n+1) s := mk_big_string n (s ++ "-- new comment\n")

section
open lean.flat_parser

def flat_p : parser_m unit :=
many1 (str "--" *> take_until (= '\n') *> any *> pure ())

end

section
open lean.parser
open lean.parser.monad_parsec

@[reducible] def parser (α : Type) : Type :=  reader_t lean.flat_parser.rec_parsers (reader_t lean.flat_parser.parser_config (parsec_t syntax (state_t parser_cache id))) α

def test_parsec (p : parser unit) (input : string) : string :=
let ps : lean.flat_parser.rec_parsers := { cmd_parser := lean.flat_parser.dummy_parser_core, term_parser := λ _, lean.flat_parser.dummy_parser_core } in
let cfg : lean.flat_parser.parser_config := { filename := "test", input := input, file_map := lean.flat_parser.file_map.from_string input, tokens := lean.parser.trie.mk } in
let r := p ps cfg input.mk_iterator {} in
match r with
| (parsec.result.ok _ it _, _)   := "OK at " ++ to_string it.offset
| (parsec.result.error msg _, _) := "Error " ++ msg.to_string

def parsec_p : parser unit :=
many1' (str "--" *> take_until (λ c, c = '\n') *> any *> pure ())
end

@[noinline] def test_flat_p (s : string) : io unit :=
io.println (lean.flat_parser.test_parser flat_p s)

@[noinline] def test_parsec_p (s : string) : io unit :=
io.println (test_parsec parsec_p s)

def prof {α : Type} (msg : string) (p : io α) : io α :=
let msg₁ := "Time for '" ++ msg ++ "':" in
let msg₂ := "Memory usage for '" ++ msg ++ "':" in
allocprof msg₂ (timeit msg₁ p)

def main (xs : list string) : io uint32 :=
let s₁ := mk_big_string xs.head.to_nat "" in
let s₂ := s₁ ++ "bad" ++ mk_big_string 20 "" in
prof "flat parser 1" (test_flat_p s₁) *>
prof "flat parser 2" (test_flat_p s₂) *>
-- prof "parsec 1" (test_parsec_p s₁) *>
-- prof "parsec 2" (test_parsec_p s₂) *>
pure 0
