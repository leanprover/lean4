import Init.Control.Except

/-!
Tests a small lexer written with (mutual) well-founded recursion over `String.Pos`.
-/

inductive Tok where
  | lpar
  | rpar
  | plus
  | minus
  | times
  | divide
  | num : Nat → Tok
  deriving Repr

structure Token where
  text : String -- Let's avoid parentheses in structures. This is legacy from Lean 3.
  tok  : Tok
  deriving Repr

inductive LexErr where
  | unexpected : Char → LexErr
  | notDigit : Char → LexErr
  deriving Repr

def Char.digit? (char : Char) : Option Nat :=
  if char.isDigit then
    some (char.toNat - '0'.toNat)
  else
    none

mutual
  def lex [Monad m] [MonadExceptOf LexErr m] {s : String} (it : s.Pos) : m (List Token) := do
    if h : it = s.endPos then
      return []
    else
      match it.get h with
      | '(' => return { text := "(", tok := Tok.lpar } :: (← lex (it.next h))
      | ')' => return { text := ")", tok := Tok.rpar } :: (← lex (it.next h))
      | '+' => return { text := "+", tok := Tok.plus } :: (← lex (it.next h))
      | other =>
        match other.digit? with
        | none   => throw <| LexErr.unexpected other
        | some d => lexnumber d [other] (it.next h)
  termination_by (it, 0)

  def lexnumber [Monad m] [MonadExceptOf LexErr m] {s : String} (soFar : Nat) (text : List Char) (it : s.Pos) : m (List Token) :=
    if h : it = s.endPos then
      return [{ text := String.ofList text.reverse, tok := Tok.num soFar }]
    else
      let c := it.get h
      match c.digit? with
      | none   => return { text := String.ofList text.reverse, tok := Tok.num soFar } :: (← lex it)
      | some d => lexnumber (soFar * 10 + d) (c :: text) (it.next h)
  termination_by (it, 1)
end

/-- info: Except.ok [] -/
#guard_msgs in
#eval lex (m := Except LexErr) "".startPos

/-- info: Except.ok [{ text := "123", tok := Tok.num 123 }] -/
#guard_msgs in
#eval lex (m := Except LexErr) "123".startPos

/--
info: Except.ok [{ text := "1", tok := Tok.num 1 }, { text := "+", tok := Tok.plus }, { text := "23", tok := Tok.num 23 }]
-/
#guard_msgs in
#eval lex (m := Except LexErr) "1+23".startPos

/--
info: Except.ok [{ text := "1", tok := Tok.num 1 },
 { text := "+", tok := Tok.plus },
 { text := "23", tok := Tok.num 23 },
 { text := "(", tok := Tok.lpar },
 { text := ")", tok := Tok.rpar }]
-/
#guard_msgs in
#eval lex (m := Except LexErr) "1+23()".startPos

namespace NonMutual

def lex [Monad m] [MonadExceptOf LexErr m] {s : String} (current? : Option (List Char × Nat)) (it : s.Pos) : m (List Token) := do
  let currTok := fun
    | (cs, n) => { text := String.ofList cs.reverse , tok := Tok.num n }
  if h : it = s.endPos then
    return current?.toList.map currTok
  else
    let emit (tok : Token) (xs : List Token) : List Token :=
      match current? with
      | none => tok :: xs
      | some numInfo => currTok numInfo :: tok :: xs;
    match it.get h with
      | '(' => return emit { text := "(", tok := Tok.lpar } (← lex none (it.next h))
      | ')' => return emit { text := ")", tok := Tok.rpar } (← lex none (it.next h))
      | '+' => return emit { text := "+", tok := Tok.plus } (← lex none (it.next h))
      | other =>
        match other.digit? with
          | none => throw <| LexErr.unexpected other
          | some d => match current? with
            | none => lex (some ([other], d)) (it.next h)
            | some (tokTxt, soFar) => lex (other :: tokTxt, soFar * 10 + d) (it.next h)
termination_by it

/-- info: Except.ok [] -/
#guard_msgs in
#eval lex (m := Except LexErr) none "".startPos

/-- info: Except.ok [{ text := "123", tok := Tok.num 123 }] -/
#guard_msgs in
#eval lex (m := Except LexErr) none "123".startPos

/--
info: Except.ok [{ text := "1", tok := Tok.num 1 }, { text := "+", tok := Tok.plus }, { text := "23", tok := Tok.num 23 }]
-/
#guard_msgs in
#eval lex (m := Except LexErr) none "1+23".startPos

/--
info: Except.ok [{ text := "1", tok := Tok.num 1 },
 { text := "+", tok := Tok.plus },
 { text := "23", tok := Tok.num 23 },
 { text := "(", tok := Tok.lpar },
 { text := ")", tok := Tok.rpar }]
-/
#guard_msgs in
#eval lex (m := Except LexErr) none "1+23()".startPos
