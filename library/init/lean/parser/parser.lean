/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Implementation for the parsec parser combinators described in the
paper:
https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/parsec-paper-letter.pdf
-/
namespace lean
namespace parser

structure position :=
(fname : string := "") (line : nat := 1) (col : nat := 0)

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

instance : has_to_string message :=
⟨message.to_string⟩

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

def test [has_to_string α] (p : parser_m α) (s : string) : string :=
match run p s with
| except.ok a := "success: " ++ to_string a
| except.error msg := to_string msg
end

def merge (msg₁ msg₂ : message) : message :=
{ expected := msg₁.expected ++ msg₂.expected, ..msg₁ }

def merge_error (msg₁ msg₂ : message) : result α :=
error (merge msg₁ msg₂) ff

def merge_ok_epsilon (a : α) (s : state) (msg₁ msg₂ : message) :=
ok_eps a s (merge msg₁ msg₂)

protected def pure (a : α) : parser_m α :=
λ s, ok_eps a s { pos := s.pos }

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
    (do try (string "let"), whitespace, ...)
    <|>
    (do try (string "fun"), whitespace, ...)
    <|>
    ...
```
Without the `try` combinator we will not be able
to backtrack on the `let` keyword.
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

/--
If the next character `c` satisfies `p`, then
update position and return `c`. Otherwise,
generate error message with current position and character.
-/
def satisfy (p : char → bool) : parser_m char :=
λ s, if !s.input.has_next then
       error { pos := s.pos, unexpected := "end of input" } ff
     else
       let c := s.input.curr in
       if !p c then
         error { pos := s.pos, unexpected := repr c } ff
       else
         let p     := s.pos in
         let new_p := if c = '\n' then { line := p.line+1, col := 0, ..p } else { col := p.col+1, ..p } in
         let new_s : state := { input := s.input.next, pos := new_p, ..s } in
         ok c new_s

def ch (c : char) : parser_m char :=
satisfy (= c)

def alpha : parser_m char :=
satisfy char.is_alpha

def digit : parser_m char :=
satisfy char.is_digit

def str_aux : nat → string.iterator → parser_m unit
| 0 it     := return ()
| (n+1) it := ch (it.curr) >> str_aux n it.next

def str (s : string) : parser_m unit :=
str_aux s.length s.mk_iterator

def remaining : parser_m nat :=
λ s, ok_eps s.input.remaining s { pos := s.pos }

def many1_aux (p : parser_m α) : nat → parser_m (list α)
| 0     := do a ← p, return [a]
| (n+1) := do a ← p,
              as ← (many1_aux n <|> return []),
              return (a::as)

def many1 (p : parser_m α) : parser_m (list α) :=
do r ← remaining, many1_aux p r

def many (p : parser_m α) : parser_m (list α) :=
many1 p <|> return []

def many1_aux' (p : parser_m α) : nat → parser_m unit
| 0     := p >> return ()
| (n+1) := p >> (many1_aux' n <|> return ())

def many1' (p : parser_m α) : parser_m unit :=
do r ← remaining, many1_aux' p r

def whitespace : parser_m unit :=
many1' (satisfy char.is_whitespace)

def eoi : parser_m unit :=
λ s, if s.input.remaining = 0 then ok_eps () s { pos := s.pos }
     else error { pos := s.pos, unexpected := repr s.input.curr, expected := ["end of input"] } ff

def sep_by1 (p : parser_m α) (sep : parser_m β) : parser_m (list α) :=
(::) <$> p <*> many (sep >> p)

def sep_by (p : parser_m α) (sep : parser_m β) : parser_m (list α) :=
sep_by1 p sep <|> return []

end parser
end lean
