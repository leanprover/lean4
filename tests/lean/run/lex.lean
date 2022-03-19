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

-- I would prefer we avoid `OptionM`, and consistely use `Except`.
-- Reason: the community is still debating whether we should go back to `Option`.
def charDigit (char : Char) :  Except String Nat :=
  match char with
    | '0' => return 0
    | '1' => return 1
    | '2' => return 2
    | '3' => return 3
    | '4' => return 4
    | '5' => return 5
    | '6' => return 6
    | '7' => return 7
    | '8' => return 8
    | '9' => return 9
    | _   => throw "digit expected"

mutual
  def lex [Monad m] [MonadExceptOf LexErr m] (it : String.Iterator) : m (List Token) := do
    if it.hasNext then
      match it.curr with
      | '(' => return { text := "(", tok := Tok.lpar } :: (← lex it.next)
      | ')' => return { text := ")", tok := Tok.rpar } :: (← lex it.next)
      | '+' => return { text := "+", tok := Tok.plus } :: (← lex it.next)
      | other =>
        match charDigit other with
        | .error _ => throw <| LexErr.unexpected other
        | .ok d    => lexnumber d [other] it.next
    else
      return []

  def lexnumber [Monad m] [MonadExceptOf LexErr m] (soFar : Nat) (text : List Char) (it : String.Iterator) : m (List Token) :=
    if it.hasNext then
      let c := it.curr
      match charDigit c with
      | .error _ => return { text := text.reverse.asString, tok := Tok.num soFar } :: (← lex it)
      | .ok d => lexnumber (soFar * 10 + d) (c :: text) it.next
    else
      return [{ text := text.reverse.asString, tok := Tok.num soFar }]
end

#eval lex (m := Except LexErr) "".iter
#eval lex (m := Except LexErr) "123".iter
#eval lex (m := Except LexErr) "1+23".iter
#eval lex (m := Except LexErr) "1+23()".iter
