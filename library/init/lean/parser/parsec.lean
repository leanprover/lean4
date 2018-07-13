/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich

Implementation for the parsec parser combinators described in the
paper:
https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/parsec-paper-letter.pdf
-/
prelude
import init.data.to_string init.data.string.basic init.data.list.basic init.control.except
import init.data.repr init.lean.name init.data.dlist init.control.monad_fail init.control.combinators
namespace lean
namespace parser
open string (iterator)

namespace parsec
@[reducible] def position : Type := nat

structure message :=
(pos        : position     := 0)
(unexpected : string       := "")          -- unexpected input
(expected   : dlist string := dlist.empty) -- expected productions

def expected.to_string : list string → string
| []       := ""
| [e]      := e
| [e1, e2] := e1 ++ " or " ++ e2
| (e::es)  := e ++ ", " ++ expected.to_string es

protected def message.to_string (input : string) (msg : message) : string :=
let (line, col) := input.line_column msg.pos in
"error at line " ++ to_string line ++ ", column " ++ to_string col ++ ":\n" ++
(if msg.unexpected = "" then "" else "unexpected " ++ msg.unexpected ++ "\n") ++
let ex_list := msg.expected.to_list in
if ex_list = [] then "" else "expected " ++ expected.to_string ex_list

def message.repr (msg : message) : string :=
"{pos := " ++ repr msg.pos ++ ", " ++
 "unexpected := " ++ repr msg.unexpected ++ ", " ++
 "expected := dlist.of_list " ++ repr msg.expected.to_list ++ "}"

instance message_has_repr : has_repr message :=
⟨message.repr⟩

/-
Remark: we store expected "error" messages in `ok_eps` results.
They contain the error that would have occurred if a
successful "epsilon" alternative was not taken.
-/
inductive result (α : Type)
| ok (a : α) (it : iterator)                               : result
| ok_eps (a : α) (it : iterator) (expected : dlist string) : result
| error {} (msg : message) (consumed : bool)               : result

@[inline] def result.mk_eps {α : Type} (a : α) (it : iterator) : result α :=
result.ok_eps a it dlist.empty
end parsec

def parsec (α : Type) :=
iterator → parsec.result α

namespace parsec
open result
variables {α β : Type}

def run (p : parsec α) (s : string) (fname := "") : except message α :=
match p s.mk_iterator with
| ok a _       := except.ok a
| ok_eps a _ _ := except.ok a
| error msg _  := except.error msg

protected def pure (a : α) : parsec α :=
λ it, mk_eps a it

def eps : parsec unit :=
parsec.pure ()

protected def failure : parsec α :=
λ it, error { unexpected := "failure", pos := it.offset } ff

def merge (msg₁ msg₂ : message) : message :=
{ expected := msg₁.expected ++ msg₂.expected, ..msg₁ }

/--
  The `bind p q` combinator behaves as follows:
  1- If `p` fails, then it fails.
  2- If `p` succeeds and consumes input, then execute `q`
  3- If `q` succeeds but does not consume input, then execute `q`
     and merge error messages if both do not consume any input.
-/
protected def bind (p : parsec α) (q : α → parsec β) : parsec β :=
λ it, match p it with
     | ok a it :=
       (match q a it with
        | ok_eps b it msg₂ := ok b it
        | error msg ff     := error msg tt
        | other            := other)
     | ok_eps a it ex₁ :=
       (match q a it with
        | ok_eps b it ex₂ := ok_eps b it (ex₁ ++ ex₂)
        | error msg₂ ff   := error { expected := ex₁ ++ msg₂.expected, .. msg₂ } ff
        | other           := other)
     | error msg c := error msg c

instance : monad parsec :=
{ bind := @parsec.bind, pure := @parsec.pure }

instance : monad_fail parsec :=
{ fail := λ _ s it, error { unexpected := s, pos := it.offset } ff }

def expect (msg : message) (exp : string) : message :=
{expected := dlist.singleton exp, ..msg}

@[inline] def label (p : parsec α) (ex : string) : parsec α :=
λ it, match p it with
      | ok_eps a it _  := ok_eps a it (dlist.singleton ex)
      | error msg ff   := error (expect msg ex) ff
      | other          := other

/--
`try p` behaves like `p`, but it pretends `p` hasn't
consumed any input when `p` fails.

It is useful for implementing infinite lookahead.
The parser `try p <|> q` will try `q` even when
`p` has consumed input.

It is also useful for specifying both the lexer and parser
together.
```
    (do try (ch 'l' >> ch 'e' >> ch 't'), whitespace, ...)
    <|>
    ...
```
Without the `try` combinator we will not be able to backtrack on the `let` keyword.
-/
def try (p : parsec α) : parsec α :=
λ it, match p it with
      | error msg _  := error msg ff
      | other        := other

/--
  The `orelse p q` combinator behaves as follows:
  1- If `p` consumed input, then return result produced by `p`
     even if it produced an error.
     Recall that the `try p` combinator can be used to
     pretend that `p` did not consume any input, and
     simulate infinite lookahead.
  2- If `p` did not consume any input, and `q` consumed
     input, then return result produced by `q`.
     Note that, `q`'s result is returned even if
     `p` succeeded without consuming input.
  3- If `p` and `q` did not consume any input, then
     it combines their error messages (even if one of
     them succeeded).
-/
protected def orelse (p q : parsec α) : parsec α :=
λ it, match p it with
      | ok_eps a it' ex₁ :=
        (match q it with
         | ok_eps _ _ ex₂ := ok_eps a it' (ex₁ ++ ex₂)
         | error msg₂ ff  := ok_eps a it' (ex₁ ++ msg₂.expected)
         | other          := other)
      | error msg₁ ff :=
        (match q it with
         | ok_eps a it' ex₂ := ok_eps a it' (msg₁.expected ++ ex₂)
         | error msg₂ ff    := error (merge msg₁ msg₂) ff
         | other            := other)
      | other              := other

instance : alternative parsec :=
{ orelse  := @parsec.orelse,
  failure := @parsec.failure }

/-- Parse `p` without consuming any input. -/
def lookahead (p : parsec α) : parsec α :=
λ it, match p it with
      | ok a s' := mk_eps a it
      | other   := other

/-- `not_followed_by p` succeeds when parser `p` fails -/
def not_followed_by (p : parsec α) (msg : string := "input") : parsec unit :=
λ it, match p it with
      | ok _ _       := error { pos := it.offset, unexpected := msg } ff
      | ok_eps _ _ _ := error { pos := it.offset, unexpected := msg } ff
      | error _ _    := mk_eps () it

def left_over : parsec iterator :=
λ it, result.mk_eps it it

@[inline] def eoi_error (pos : position) : result α :=
result.error { pos := pos, unexpected := "end of input" } ff

@[inline] def satisfy (p : char → bool) : parsec char :=
λ it,
  if !it.has_next then eoi_error it.offset
  else let c := it.curr in
      if p c then result.ok c it.next
      else result.error { pos := it.offset, unexpected := repr c } ff

private def str_aux : nat → iterator → iterator → option iterator
| 0     _    it := some it
| (n+1) s_it it :=
  if it.has_next ∧ s_it.curr = it.curr then str_aux n s_it.next it.next
  else none

def str (s : string) : parsec string :=
if s.is_empty then pure ""
else λ it, match str_aux s.length s.mk_iterator it with
  | some it' := result.ok s it'
  | none     := result.error { pos := it.offset, expected := dlist.singleton (repr s) } ff

private def take_aux : nat → string → iterator → result string
| 0     r it := result.ok r it
| (n+1) r it :=
  if !it.has_next then eoi_error it.offset
  else take_aux n (r.push (it.curr)) it.next

def take (n : nat) : parsec string :=
if n = 0 then pure ""
else take_aux n ""

@[inline] private def mk_string_result (r : string) (it : iterator) : result string :=
if r.is_empty then result.mk_eps r it
else result.ok r it

private def take_while_aux (p : char → bool) : nat → string → parsec string
| 0     r it := mk_string_result r it
| (n+1) r it :=
  if !it.has_next then mk_string_result r it
  else let c := it.curr in
       if p c then take_while_aux n (r.push c) it.next
       else mk_string_result r it

def take_while_cont (p : char → bool) (ini : string) : parsec string :=
λ it, take_while_aux p it.remaining ini it

@[inline] private def mk_consumed_result (consumed : bool) (it : iterator) : result unit :=
if consumed then result.ok () it
else result.mk_eps () it

private def take_while_aux' (p : char → bool) : nat → bool → iterator → result unit
| 0     consumed it := mk_consumed_result consumed it
| (n+1) consumed it :=
  if !it.has_next then mk_consumed_result consumed it
  else let c := it.curr in
       if p c then take_while_aux' n tt it.next
       else mk_consumed_result consumed it

def take_while' (p : char → bool) : parsec unit :=
λ it, take_while_aux' p it.remaining ff it

def observing (p : parsec α) : parsec (except message α) :=
λ it, match p it with
      | ok a it'        := ok (except.ok a) it'
      | ok_eps a it' ex := ok_eps (except.ok a) it' ex
      | error msg _     := ok (except.error msg) it

private def pos_of : result α → nat
| (ok _ it)       := it.offset
| (ok_eps _ it _) := it.offset
| (error msg _)   := msg.pos

private def merge_errors : result α → result α → result α
| (error msg ff) (error msg' ff) := error (merge msg msg') ff
| r              _               := r

def longest_match (ps : list (parsec α)) : parsec α :=
λ it, ps.foldl (λ r p,
  let r' := p it in if pos_of r ≥ pos_of r'
  then merge_errors r r'
  else merge_errors r' r) (parsec.failure it)

def error (unexpected : string := "") (expected : dlist string := dlist.empty) (pos : option position := none) : parsec α :=
λ it, error { unexpected := unexpected, expected := expected, pos := pos.get_or_else it.offset } ff
end parsec


/-- Type class for abstracting from concrete monad stacks containing a `parsec` somewhere. -/
class monad_parsec (m : Type → Type) :=
(error {} {α : Type} (unexpected : string := "") (expected : dlist string := dlist.empty)
  (pos : option parsec.position := none) : m α)
(left_over {} : m iterator)
(label {α : Type} (p : m α) (expected : string) : m α)
/-
`try p` behaves like `p`, but it pretends `p` hasn't
consumed any input when `p` fails.

It is useful for implementing infinite lookahead.
The parser `try p <|> q` will try `q` even when
`p` has consumed input.

It is also useful for specifying both the lexer and parser
together.
```
    (do try (ch 'l' >> ch 'e' >> ch 't'), whitespace, ...)
    <|>
    ...
```
Without the `try` combinator we will not be able to backtrack on the `let` keyword.
-/
(try {α : Type} (p : m α) : m α)
/- Parse `p` without consuming any input. -/
(lookahead {α : Type} (p : m α) : m α)
/-
If the next character `c` satisfies `p`, then
update position and return `c`. Otherwise,
generate error message with current position and character. -/
(satisfy {} (p : char → bool) : m char)
/-
`str s` parses a sequence of elements that match `s`. Returns the parsed string (i.e. `s`).
This parser consumes no input if it fails (even if a partial match).
Note: The behaviour of this parser is different to that the `string` parser in the Parsec Haskell library,
as this one is all-or-nothing.
-/
(str {} (s : string) : m string)
/- Consume `n` characters. -/
(take {} (n : nat) : m string)
(take_while_cont {} (p : char → bool) (ini : string) : m string)
/- Similar to `take_while` but it does not return the consumed input. -/
(take_while' {} (p : char → bool) : m unit)
/- Parse `p`, returning errors explicitly.
   If `p` does not fail, `observing p` behaves like `except.ok <$> p`. -/
(observing {} {α : Type} (p : m α) : m (except parsec.message α))
/- Execute all parsers in `ps` and return the result of the longest parse,
   regardless of whether it was successful. If there are two parses of
   equal length, the first parse wins. -/
(longest_match {} {α : Type} (ps : list (m α)) : m α)

open monad_parsec

instance {m : Type → Type} [monad m] : monad_parsec parsec :=
⟨@parsec.error, @parsec.left_over, @parsec.label, @parsec.try, @parsec.lookahead, @parsec.satisfy,
 @parsec.str, @parsec.take, @parsec.take_while_cont, @parsec.take_while', @parsec.observing,
 @parsec.longest_match⟩

def monad_parsec_trans (m n : Type → Type) [has_monad_lift m n] [monad_functor m m n n] [monad_parsec m] [monad n] [has_orelse n] (observing longest_match) : monad_parsec n :=
{ error := λ α un ex pos, monad_lift (error un ex pos : m _),
  left_over := monad_lift (left_over : m _),
  label := λ α p ex, monad_map (λ α (p : m α), label p ex) p,
  try := λ α, monad_map (@try m _),
  lookahead := λ α, monad_map (@try m _),
  satisfy := λ p, monad_lift (satisfy p : m _),
  str := λ s, monad_lift (str s : m _),
  take := λ n, monad_lift (take n : m _),
  take_while_cont := λ p ini, monad_lift (take_while_cont p ini : m _),
  take_while' := λ p, monad_lift (take_while' p : m _),
  observing := observing,
  longest_match := longest_match }

instance reader_t.monad_parsec (ρ m) [monad m] [alternative m] [monad_parsec m] : monad_parsec (reader_t ρ m) :=
monad_parsec_trans m _
(λ α p, ⟨λ r, observing (p.run r)⟩)
(λ α ps, ⟨λ r, longest_match (ps.map (λ p, p.run r))⟩)

instance state_t.monad_parsec (σ m) [monad m] [alternative m] [monad_parsec m] : monad_parsec (state_t σ m) :=
monad_parsec_trans m _
(λ α p, ⟨λ st,
  do ex ← observing (p.run st),
     match ex with
     | except.ok (a, st') := pure (except.ok a, st')
     | except.error e    := pure (except.error e, st)⟩)
(λ α ps, ⟨λ st,
   longest_match (ps.map (λ p, p.run st))⟩)

namespace monad_parsec
open parsec
variables {m : Type → Type} [monad m] [monad_parsec m] [alternative m] {α β : Type}

infixr ` <?> `:2 := label

/-- Faster version of `not_followed_by (satisfy p)` -/
@[inline] def not_followed_by_sat (p : char → bool) : m unit :=
do it ← left_over,
   if !it.has_next then pure ()
   else let c := it.curr in
       if p c then error (repr c)
       else pure ()

def curr : m char :=
string.iterator.curr <$> left_over

@[inline] def cond (p : char → bool) (t : m α) (e : m α) : m α :=
mcond (p <$> curr) t e

def ch (c : char) : m char :=
satisfy (= c)

def alpha : m char :=
satisfy char.is_alpha

def digit : m char :=
satisfy char.is_digit

def upper : m char :=
satisfy char.is_upper

def lower : m char :=
satisfy char.is_lower

def any : m char :=
satisfy (λ _, true)

/--
Consume input as long as the predicate returns `tt`, and return the consumed input.
This parser does not fail. It will return an empty string if the predicate
returns `ff` on the current character. -/
def take_while (p : char → bool) : m string :=
take_while_cont p ""

/--
Consume input as long as the predicate returns `tt`, and return the consumed input.
This parser requires the predicate to succeed on at least once. -/
def take_while1 (p : char → bool) : m string :=
do c ← satisfy p,
   take_while_cont p (to_string c)

/--
Consume input as long as the predicate returns `ff` (i.e. until it returns `tt`), and return the consumed input.
This parser does not fail. -/
def take_until (p : char → bool) : m string :=
take_while (λ c, !p c)

def take_until1 (p : char → bool) : m string :=
take_while1 (λ c, !p c)

/-- Similar to `take_while1` but it does not return the consumed input. -/
def take_while1' (p : char → bool) : m unit :=
satisfy p *> take_while' p

/-- Consume zero or more whitespaces. -/
def whitespace : m unit :=
take_while' char.is_whitespace

/-- Shorthand for `p <* whitespace` -/
def lexeme (p : m α) : m α :=
p <* whitespace

/-- Parse a numeral in decimal. -/
def num : m nat :=
string.to_nat <$> (take_while1 char.is_digit)

/-- Return the number of characters left to be parsed. -/
def remaining : m nat :=
string.iterator.remaining <$> left_over

/-- Succeed only if there are at least `n` characters left. -/
def ensure (n : nat) : m unit :=
do it ← left_over,
   if n ≤ it.remaining then pure ()
   else error "end of input" (dlist.singleton ("at least " ++ to_string n ++ " characters"))

/-- Return the current position. -/
def pos : m position :=
string.iterator.offset <$> left_over

def many1_aux (p : m α) : nat → m (list α)
| 0     := do a ← p, return [a]
| (n+1) := do a ← p,
              as ← (many1_aux n <|> return []),
              return (a::as)

def many1 (p : m α) : m (list α) :=
do r ← remaining, many1_aux p r

def many (p : m α) : m (list α) :=
many1 p <|> return []

def many1_aux' (p : m α) : nat → m unit
| 0     := p >> return ()
| (n+1) := p >> (many1_aux' n <|> return ())

def many1' (p : m α) : m unit :=
do r ← remaining, many1_aux' p r

def many' (p : m α) : m unit :=
many1' p <|> return ()

def eoi : m unit :=
do it ← left_over,
   if it.remaining = 0 then pure ()
   else error (repr it.curr) (dlist.singleton ("end of input"))

def sep_by1 (p : m α) (sep : m β) : m (list α) :=
(::) <$> p <*> many (sep >> p)

def sep_by (p : m α) (sep : m β) : m (list α) :=
sep_by1 p sep <|> return []

def fix_aux (f : m α → m α) : nat → m α
| 0     := failure
| (n+1) := f (fix_aux n)

def fix (f : m α → m α) : m α :=
do n ← remaining, fix_aux f (n+1)

def foldr_aux (f : α → β → β) (p : m α) (b : β) : nat → m β
| 0     := return b
| (n+1) := (f <$> p <*> foldr_aux n) <|> return b

/-- Matches zero or more occurrences of `p`, and folds the result. -/
def foldr (f : α → β → β) (p : m α) (b : β) : m β :=
do it ← left_over,
   foldr_aux f p b it.remaining

def foldl_aux (f : α → β → α) (p : m β) : α → nat → m α
| a 0     := return a
| a (n+1) := (do x ← p, foldl_aux (f a x) n) <|> return a

/-- Matches zero or more occurrences of `p`, and folds the result. -/
def foldl (f : α → β → α) (a : α) (p : m β) : m α :=
do it ← left_over,
   foldl_aux f p a it.remaining

def unexpected (msg : string) : m α :=
error msg

def unexpected_at (msg : string) (pos : position) : m α :=
error msg dlist.empty pos
end monad_parsec

namespace parsec
open monad_parsec
variables {m : Type → Type} [monad m] {α β : Type}

def parse (p : parsec α) (s : string) (fname := "") : except message α :=
run p s fname

def parse_with_eoi (p : parsec α) (s : string) (fname := "") : except message α :=
run (p <* eoi) s fname

def parse_with_left_over (p : parsec α) (s : string) (fname := "") : except message (α × iterator) :=
run (prod.mk <$> p <*> left_over) s fname

end parsec
end parser
end lean
