import Init.Control.Except

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
  def lex [Monad m] [MonadExceptOf LexErr m] (it : String.Iterator) : m (List Token) := do
    if it.hasNext then
      match it.curr with
      | '(' => return { text := "(", tok := Tok.lpar } :: (← lex it.next)
      | ')' => return { text := ")", tok := Tok.rpar } :: (← lex it.next)
      | '+' => return { text := "+", tok := Tok.plus } :: (← lex it.next)
      | other =>
        match other.digit? with
        | none   => throw <| LexErr.unexpected other
        | some d => lexnumber d [other] it.next
    else
      return []

  def lexnumber [Monad m] [MonadExceptOf LexErr m] (soFar : Nat) (text : List Char) (it : String.Iterator) : m (List Token) :=
    if it.hasNext then
      let c := it.curr
      match c.digit? with
      | none   => return { text := text.reverse.asString, tok := Tok.num soFar } :: (← lex it)
      | some d => lexnumber (soFar * 10 + d) (c :: text) it.next
    else
      return [{ text := text.reverse.asString, tok := Tok.num soFar }]
end

#eval lex (m := Except LexErr) "".iter
#eval lex (m := Except LexErr) "123".iter
#eval lex (m := Except LexErr) "1+23".iter
#eval lex (m := Except LexErr) "1+23()".iter

def Option.toList : Option α -> List α
  | none   => []
  | some x => [x]

namespace NonMutual

def lex [Monad m] [MonadExceptOf LexErr m] (current? : Option (List Char × Nat)) (it : String.Iterator) : m (List Token) := do
  let currTok := fun
    | (cs, n) => { text := {data := cs.reverse}, tok := Tok.num n }
  if it.hasNext then
    let emit (tok : Token) (xs : List Token) : List Token :=
      match current? with
      | none => tok :: xs
      | some numInfo => currTok numInfo :: tok :: xs;
    match it.curr with
      | '(' => return emit { text := "(", tok := Tok.lpar } (← lex none it.next)
      | ')' => return emit { text := ")", tok := Tok.rpar } (← lex none it.next)
      | '+' => return emit { text := "+", tok := Tok.plus } (← lex none it.next)
      | other =>
        match other.digit? with
          | none => throw <| LexErr.unexpected other
          | some d => match current? with
            | none => lex (some ([other], d)) it.next
            | some (tokTxt, soFar) => lex (other :: tokTxt, soFar * 10 + d) it.next
  else
    return current?.toList.map currTok

#eval lex (m := Except LexErr) none "".iter
#eval lex (m := Except LexErr) none "123".iter
#eval lex (m := Except LexErr) none "1+23".iter
#eval lex (m := Except LexErr) none "1+23()".iter
