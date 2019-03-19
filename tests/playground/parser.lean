namespace lean
namespace parser

abbrev pos := string.utf8_pos

/-
σ  is the non-backtrackable state
δ  is the backtrackable state
μ  is the extra error message data
-/
inductive result (σ δ μ α : Type)
| ok    {} (a : α)        (i : pos) (st : σ) (bst : δ)          (eps : bool) : result
| error {} (msg : string) (i : pos) (st : σ) (extra : option μ) (eps : bool) : result

inductive result.is_ok {σ δ μ α : Type} : result σ δ μ α → Prop
| mk (a : α) (i : pos) (st : σ) (bst : δ) (eps : bool) : result.is_ok (result.ok a i st bst eps)

theorem error_is_not_ok {σ δ μ α : Type} {msg : string} {i : pos} {st : σ} {extra : option μ} {eps : bool}
                        (h : result.is_ok (@result.error σ δ μ α msg i st extra eps)) : false :=
match h with end

@[inline] def unreachable_error {σ δ μ α β : Type} {msg : string} {i : pos} {st : σ} {extra : option μ} {eps : bool}
                                (h : result.is_ok (@result.error σ δ μ α msg i st extra eps)) : β :=
false.elim (error_is_not_ok h)

def input (σ δ μ : Type) : Type := { r : result σ δ μ unit // r.is_ok }

@[inline] def mk_input {σ δ μ : Type} (i : pos) (st : σ) (bst : δ) (eps := tt) : input σ δ μ :=
⟨result.ok () i st bst eps, result.is_ok.mk _ _ _ _ _⟩

def parser_m (σ δ μ α : Type) :=
string → input σ δ μ → result σ δ μ α

variables {σ δ μ α β : Type}

@[inline] def parser_m.run (p : parser_m σ δ μ α) (st : σ) (bst : δ) (s : string) : result σ δ μ α :=
p s (mk_input 0 st bst)

@[inline] def parser_m.pure (a : α) : parser_m σ δ μ α :=
λ _ inp,
  match inp with
  | ⟨result.ok _ it st bst _, h⟩ := result.ok a it st bst tt
  | ⟨result.error _ _ _ _ _, h⟩  := unreachable_error h

@[inline_if_reduce] def strict_or  (b₁ b₂ : bool) := b₁ || b₂
@[inline_if_reduce] def strict_and (b₁ b₂ : bool) := b₁ && b₂

@[inline] def parser_m.bind (x : parser_m σ δ μ α) (f : α → parser_m σ δ μ β) : parser_m σ δ μ β :=
λ str inp,
  match x str inp with
  | result.ok a i st bst e₁ :=
    (match f a str (mk_input i st bst) with
     | result.ok b i st bst e₂      := result.ok b i st bst (strict_and e₁ e₂)
     | result.error msg i st ext e₂ := result.error msg i st ext (strict_and e₁ e₂))
  | result.error msg i st etx e  := result.error msg i st etx e

instance parser_m_is_monad : monad (parser_m σ δ μ) :=
{pure := @parser_m.pure _ _ _, bind := @parser_m.bind _ _ _}

def mk_error (r : input σ δ μ) (msg : string) (eps := tt) : result σ δ μ α :=
match r with
| ⟨result.ok _ i c s _, _⟩    := result.error msg i c none eps
| ⟨result.error _ _ _ _ _, h⟩ := unreachable_error h

@[inline] def parser_m.orelse (p q : parser_m σ δ μ α) : parser_m σ δ μ α :=
λ str inp,
  match inp with
  | ⟨result.ok _ i₁ _ bst₁ _, _⟩ :=
    (match p str inp with
     | result.error _ _ st₂ _ tt := q str (mk_input i₁ st₂ bst₁)
     | other                     := other)
  | ⟨result.error _ _ _ _ _, h⟩ := unreachable_error h

@[inline] def parser_m.failure : parser_m σ δ μ α :=
λ _ inp, mk_error inp "failure"

instance : alternative (parser_m σ δ μ) :=
{ orelse         := @parser_m.orelse _ _ _,
  failure        := @parser_m.failure _ _ _,
  .. parser.parser_m_is_monad }

def set_silent_error : result σ δ μ α → result σ δ μ α
| (result.error msg i st ext _) := result.error msg i st ext tt
| other                         := other

@[inline] def curr (str : string) (i : pos) : char   := str.utf8_get i
@[inline] def next (str : string) (i : pos) : pos    := str.utf8_next i
@[inline] def at_end (str : string) (i : pos) : bool := str.utf8_at_end i

@[inline] def curr_pos : input σ δ μ → pos
| ⟨result.ok _ i _ _ _, _⟩    := i
| ⟨result.error _ _ _ _ _, h⟩ := unreachable_error h

namespace prim
@[inline] def try {α : Type} (p : parser_m σ δ μ α) : parser_m σ δ μ α :=
λ str inp, set_silent_error (p str inp)

@[inline] def lookahead (p : parser_m σ δ μ α) : parser_m σ δ μ α :=
λ str inp,
  match inp with
  | ⟨result.ok _ i _ bst _, _⟩ :=
    (match p str inp with
     | result.ok a _ st _ _ := result.ok a i st bst tt
     | other                := other)
  | ⟨result.error _ _ _ _ _, h⟩ := unreachable_error h

@[specialize] def satisfy (p : char → bool) : parser_m σ δ μ char :=
λ str inp,
  match inp with
  | ⟨result.ok _ i st bst _, _⟩ :=
    if at_end str i then mk_error inp "end of input"
    else let c := curr str i in
         if p c then result.ok c (next str i) st bst ff
         else mk_error inp "unexpected character"
  | ⟨result.error _ _ _ _ _, h⟩ := unreachable_error h

@[specialize] def take_until_aux (p : char → bool) : nat → parser_m σ δ μ unit
| 0     str inp := inp.val
| (n+1) str inp :=
  match inp with
  | ⟨result.ok _ i st bst _, _⟩ :=
    if at_end str i then inp.val
    else let c := curr str i in
         if p c then inp.val
         else take_until_aux n str (mk_input (next str i) st bst ff)
  | ⟨result.error _ _ _ _ _, h⟩ := unreachable_error h

@[inline] def take_until (p : char → bool) : parser_m σ δ μ unit :=
λ str inp, take_until_aux p str.length str inp

def str_aux (in_s : string) (s : string) (error_msg : string) : nat → input σ δ μ → pos → result σ δ μ unit
| 0     inp j := mk_error inp error_msg
| (n+1) inp j :=
  if at_end s j then inp.val
  else
    match inp with
    | ⟨result.ok _ i st bst e, _⟩ :=
      if at_end in_s i then mk_error inp error_msg
      else if curr in_s i = curr s j then str_aux n (mk_input (next in_s i) st bst ff) (next s j)
      else mk_error inp error_msg
    | ⟨result.error _ _ _ _ _, h⟩ := unreachable_error h

@[inline] def str (s : string) : parser_m σ δ μ unit :=
λ in_str inp, str_aux in_str s ("expected '" ++ repr s ++ "'") in_str.length inp 0

@[specialize] def many_loop (a : α) (p : parser_m σ δ μ α) : nat → bool → parser_m σ δ μ α
| 0     fst := pure a
| (k+1) fst := λ str inp,
  match inp with
  | ⟨result.ok _ i₀ _ bst₀ _, _⟩ :=
    (match p str inp with
     | result.ok _ i st bst _   := many_loop k ff str (mk_input i st bst)
     | result.error _ _ st _ _  := result.ok a i₀ st bst₀ fst)
  | ⟨result.error _ _ _ _ _, h⟩ := unreachable_error h

-- Auxiliary function used to lift many_aux
@[inline] def many_aux (a : α) (p : parser_m σ δ μ α) : parser_m σ δ μ α :=
λ str inp, many_loop a p str.length tt str inp

@[inline] def many (p : parser_m σ δ μ unit) : parser_m σ δ μ unit  :=
many_aux () p

@[inline] def many1 (p : parser_m σ δ μ unit) : parser_m σ δ μ unit  :=
p *> many p

end prim

class monad_parser (σ : out_param Type) (δ : out_param Type) (μ : out_param Type) (m : Type → Type) :=
(lift {} {α : Type} : parser_m σ δ μ α → m α)
(map {} {α : Type} : (Π β, parser_m σ δ μ β → parser_m σ δ μ β) → m α → m α)

instance monad_parser_base : monad_parser σ δ μ (parser_m σ δ μ) :=
{ lift := λ α, id,
  map  := λ α f x, f α x }

instance monad_parser_trans {m n : Type → Type} [has_monad_lift m n] [monad_functor m m n n] [monad_parser σ δ μ m] : monad_parser σ δ μ n :=
{ lift := λ α p, monad_lift (monad_parser.lift p : m α),
  map  := λ α f x, monad_map (λ β x, (monad_parser.map @f x : m β)) x }

class monad_parser_aux (σ : out_param Type) (δ : out_param Type) (μ : out_param Type) (m : Type → Type) :=
(map {} {α : Type} : (parser_m σ δ μ α → parser_m σ δ μ α) → m α → m α)

instance monad_parser_aux_base : monad_parser_aux σ δ μ (parser_m σ δ μ) :=
{ map  := λ α, id }

instance monad_parser_aux_reader {m : Type → Type} {ρ : Type} [monad m] [monad_parser_aux σ δ μ m] : monad_parser_aux σ δ μ (reader_t ρ m) :=
{ map  := λ α f x r, (monad_parser_aux.map f : m α → m α) (x r) }

section
variables {m : Type → Type} [monad_parser σ δ μ m]

@[inline] def satisfy (p : char → bool) : m char := monad_parser.lift (prim.satisfy p)
def ch (c : char) : m char := satisfy (= c)
def alpha : m char := satisfy char.is_alpha
def digit : m char := satisfy char.is_digit
def upper : m char := satisfy char.is_upper
def lower : m char := satisfy char.is_lower
def any   : m char := satisfy (λ _, true)

@[inline] def take_until (p : char → bool) : m unit := monad_parser.lift (prim.take_until p)

@[inline] def str (s : string) : m unit := monad_parser.lift (prim.str s)

@[inline] def lookahead (p : m α) : m α :=
monad_parser.map (λ β p, prim.lookahead p) p

@[inline] def take_while (p : char → bool) : m unit := take_until (λ c, !p c)

@[inline] def whitespace : m unit := take_while char.is_whitespace

end

section
variables {m : Type → Type} [monad_parser_aux σ δ μ m]

@[inline] def many (p : m unit) : m unit  := monad_parser_aux.map prim.many p
@[inline] def many1 (p : m unit) : m unit := monad_parser_aux.map prim.many1 p

end

end parser
end lean

abbrev parser := reader_t nat (lean.parser.parser_m unit unit unit) unit

open lean.parser

-- set_option pp.implicit true
-- set_option trace.compiler.boxed true

def test_p : parser :=
many1 (str "++" <|> str "**" <|> (str "--" *> take_until (= '\n') *> any *> pure ()))

def test_parser (x : parser) (input : string) : string :=
match (x 0).run () () input with
| lean.parser.result.ok _ i _ _ _      := "Ok at " ++ to_string i
| result.error msg i _ _ _ := "Error at " ++ to_string i ++ ": " ++ msg

@[noinline] def test (s : string) : io unit :=
io.println (test_parser test_p s)

def mk_big_string : nat → string → string
| 0     s := s
| (n+1) s := mk_big_string n (s ++ "-- new comment\n")

def prof {α : Type} (msg : string) (p : io α) : io α :=
let msg₁ := "Time for '" ++ msg ++ "':" in
let msg₂ := "Memory usage for '" ++ msg ++ "':" in
allocprof msg₂ (timeit msg₁ p)

def main (xs : list string) : io unit :=
let s₁ := mk_big_string xs.head.to_nat "" in
let s₂ := s₁ ++ "bad" ++ mk_big_string 20 "" in
prof "parser 1" (test s₁) *>
prof "parser 2" (test s₂)
