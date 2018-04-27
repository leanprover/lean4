/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Implementation for the parsec parser combinators described in the
paper:
https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/parsec-paper-letter.pdf
-/
prelude
import init.data.to_string init.data.string.basic init.data.list.basic init.control.except
import init.data.repr
namespace lean
namespace parser

structure position :=
(fname : string := "") (line : nat := 1) (col : nat := 0)

def position.repr (p : position) : string :=
if p.fname = "" then "{line := " ++ repr p.line ++ ", col := " ++ repr p.col ++ "}"
else "{fname := " ++ repr p.fname ++ ", line := " ++ repr p.line ++ ", col := " ++ repr p.col ++ "}"

instance position_has_repr : has_repr position :=
⟨position.repr⟩

structure state :=
(input : string.iterator)
(pos   : position)

structure message :=
(pos        : position    := {})
(unexpected : string      := "")      -- unexpected input
(expected   : list string := []) -- expected productions

def expected.to_string : list string → string
| []       := ""
| [e]      := e
| [e1, e2] := e1 ++ " or " ++ e2
| (e::es)  := e ++ ", " ++ expected.to_string es

def message.to_string (msg : message) : string :=
"error at (line : " ++ to_string msg.pos.line ++ ", column: " ++ to_string msg.pos.col ++ ")\n" ++
"unexpected " ++ msg.unexpected ++ "\n" ++
if msg.expected = [] then "" else "expected " ++ expected.to_string msg.expected

instance message_has_to_string : has_to_string message :=
⟨message.to_string⟩

def message.repr (msg : message) : string :=
"{pos := " ++ repr msg.pos ++ ", " ++
 "unexpected := " ++ repr msg.unexpected ++ ", " ++
 "expected := " ++ repr msg.expected ++ "}"

instance message_has_repr : has_repr message :=
⟨message.repr⟩

/-
Remark: we store error messages in `ok_eps` results.
They contain the error that would have occurred if a
successful "epsilon" alternative was not taken.
-/
inductive result (α : Type)
| ok (a : α) (s : state)                     : result
| ok_eps (a : α) (s : state) (msg : message) : result
| error {} (msg : message) (consumed : bool) : result

open result

def parser_m (α : Type) :=
state → result α

variables {α β : Type}

def run (p : parser_m α) (s : string) (fname := "") : except message α :=
match p {pos := {fname := fname}, input := s.mk_iterator} with
| ok a _       := except.ok a
| ok_eps a _ _ := except.ok a
| error msg _  := except.error msg
end

def merge (msg₁ msg₂ : message) : message :=
{ expected := msg₁.expected ++ msg₂.expected, ..msg₁ }

def merge_error (msg₁ msg₂ : message) : result α :=
error (merge msg₁ msg₂) ff

def merge_ok_epsilon (a : α) (s : state) (msg₁ msg₂ : message) :=
ok_eps a s (merge msg₁ msg₂)

protected def pure (a : α) : parser_m α :=
λ s, ok_eps a s { pos := s.pos }

def eps : parser_m unit :=
parser.pure ()

/--
  The `bind p q` combinator behaves as follows:
  1- If `p` fails, then it fails.
  2- If `p` succeeds and consumes input, then execute `q`
  3- If `q` succeeds but does not consume input, then execute `q`
     and merge error messages if both do not consume any input.
-/
protected def bind (p : parser_m α) (q : α → parser_m β) : parser_m β :=
λ s, match p s with
     | ok a s :=
       match q a s with
       | ok_eps b s msg₂ := ok b s
       | error msg ff    := error msg tt
       | other           := other
       end
     | ok_eps a s msg₁ :=
       match q a s with
       | ok_eps b s msg₂ := merge_ok_epsilon b s msg₁ msg₂
       | error msg₂ ff   := merge_error msg₂ msg₁
       | other           := other
       end
     | error msg c := error msg c
     end

instance : monad parser_m :=
{ bind := @parser.bind, pure := @parser.pure }

def expect (msg : message) (exp : string) : message :=
{expected := [exp], ..msg}

@[inline] def label (p : parser_m α) (exp : string) : parser_m α :=
λ s, match p s with
     | ok_eps a s msg := ok_eps a s (expect msg exp)
     | error msg ff   := error (expect msg exp) ff
     | other          := other
     end

infixr ` <?> `:2 := label

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
def try (p : parser_m α) : parser_m α :=
λ s, match p s with
     | error msg _  := error msg ff
     | other        := other
     end

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
protected def orelse (p q : parser_m α) : parser_m α :=
λ s, match p s with
     | ok_eps a s' msg₁ :=
       match q s with
       | ok_eps _ _ msg₂ := merge_ok_epsilon a s' msg₁ msg₂
       | error msg₂ ff   := merge_ok_epsilon a s' msg₁ msg₂
       | other           := other
       end
     | error msg₁ ff :=
       match q s with
       | ok_eps a s' msg₂ := merge_ok_epsilon a s' msg₁ msg₂
       | error msg₂ ff    := merge_error msg₁ msg₂
       | other            := other
       end
     | other              := other
     end

instance : has_orelse parser_m :=
{ orelse := @parser.orelse }

@[inline] def next_pos (c : char) (p : position) : position :=
if c = '\n'
then { line := p.line+1, col := 0, ..p }
else { col := p.col+1, ..p }

@[inline] def eoi_error (pos : position) : result α :=
error { pos := pos, unexpected := "end of input" } ff

/--
If the next character `c` satisfies `p`, then
update position and return `c`. Otherwise,
generate error message with current position and character.
-/
@[inline] def satisfy (p : char → bool) : parser_m char :=
λ s, if !s.input.has_next then
       eoi_error s.pos
     else
       let c := s.input.curr in
       if !p c then
         error { pos := s.pos, unexpected := repr c } ff
       else
         ok c { input := s.input.next, pos := next_pos c s.pos, ..s }

def ch (c : char) : parser_m char :=
satisfy (= c)

def alpha : parser_m char :=
satisfy char.is_alpha

def digit : parser_m char :=
satisfy char.is_digit

def upper : parser_m char :=
satisfy char.is_upper

def lower : parser_m char :=
satisfy char.is_lower

def any : parser_m char :=
λ s, if !s.input.has_next then
       error { pos := s.pos, unexpected := "end of input" } ff
     else
       let c     := s.input.curr in
       ok c { input := s.input.next, pos := next_pos c s.pos, ..s }

private def str_aux (s : string) : nat → string.iterator → string.iterator → position → result string
| 0 it input pos     := ok s { input := input, pos := pos }
| (n+1) it input pos :=
  if !input.has_next then
    eoi_error pos
  else
    let c := input.curr in
    if it.curr = c then str_aux n it.next input.next (next_pos c pos)
    else error { pos := pos, unexpected := repr c } ff

/--
`str s` parses a sequence of elements that match `s`. Returns the parsed string (i.e. `s`).
This parser consumes no input if it fails (even if a partial match).
Note: The behaviour of this parser is different to that the `string` parser in the Parsec Haskell library,
as this one is all-or-nothing.
-/
def str (s : string) : parser_m string :=
λ st, str_aux s s.length s.mk_iterator st.input st.pos

def remaining : parser_m nat :=
λ s, ok_eps s.input.remaining s { pos := s.pos }

def left_over : parser_m string.iterator :=
λ s, ok_eps s.input s { pos := s.pos }

def many1_aux (p : parser_m α) : nat → parser_m (list α)
| 0     := do a ← p, return [a]
| (n+1) := do a ← p,
              as ← (many1_aux n <|> return []),
              return (a::as)

def many1 (p : parser_m α) : parser_m (list α) :=
do r ← remaining, many1_aux p r

def many (p : parser_m α) : parser_m (list α) :=
many1 p <* eps

def many1_aux' (p : parser_m α) : nat → parser_m unit
| 0     := p >> return ()
| (n+1) := p >> (many1_aux' n <|> return ())

def many1' (p : parser_m α) : parser_m unit :=
do r ← remaining, many1_aux' p r

def many' (p : parser_m α) : parser_m unit :=
many1' p <* eps

def whitespace : parser_m unit :=
many' (satisfy char.is_whitespace)

def lexeme (p : parser_m α) : parser_m α :=
p <* whitespace

def digits_to_nat : nat → list char → nat
| r []      := r
| r (d::ds) := digits_to_nat (r*10 + d.to_nat - '0'.to_nat) ds

def num : parser_m nat :=
(digits_to_nat 0) <$> many1 digit

def eoi : parser_m unit :=
λ s, if s.input.remaining = 0 then ok_eps () s { pos := s.pos }
     else error { pos := s.pos, unexpected := repr s.input.curr, expected := ["end of input"] } ff

def sep_by1 (p : parser_m α) (sep : parser_m β) : parser_m (list α) :=
(::) <$> p <*> many (sep >> p)

def sep_by (p : parser_m α) (sep : parser_m β) : parser_m (list α) :=
sep_by1 p sep <|> return []

def parse (p : parser_m α) (s : string) (fname := "") : except message α :=
run p s fname

def parse_with_eoi (p : parser_m α) (s : string) (fname := "") : except message α :=
run (p <* eoi) s fname

def parse_with_left_over (p : parser_m α) (s : string) (fname := "") : except message (α × string.iterator) :=
run (prod.mk <$> p <*> left_over) s fname

end parser
end lean
