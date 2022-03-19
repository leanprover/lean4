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

-- Remask: Lean has auto implicit arguments, you don't need {α}
-- def cons (x : α) : List α → List α := fun xs => x :: xs
-- We can also use
open List (cons)

-- Moved `lex` example to the end.

mutual
  def lex2 [Monad m] [MonadExceptOf LexErr m] (input : List Char) : m (List Token) := do
    match input with
      | [] => pure []
      | c :: cs =>
        match c with
          | '(' => return { text := "(", tok := Tok.lpar } :: (← lex2 cs)  -- Let's always use `return` and the nested method notation.
          | ')' => return { text := ")", tok := Tok.rpar } :: (← lex2 cs)
          | '+' => return { text := "+", tok := Tok.plus } :: (← lex2 cs)
          | other =>
            match charDigit other with
              -- Lean can infer the namespace of constructors using the expected type. `.error` here is just shorthand for `Except.error`
              | .error _ => throw <| LexErr.unexpected other -- Let's avoid `$`. We still support if for old Lean users and Haskell users, but we are now using the F# `<|`.
              | .ok d    => lex2number d [other] cs -- It was `input` here, I believe it was a typo

  def lex2number [Monad m] [MonadExceptOf LexErr m] (soFar : Nat) (text : List Char) (input : List Char) : m (List Token) :=
    match input with
      | [] => return [{ text := { data := text.reverse }, tok := Tok.num soFar }] -- We always use space after `{` and before `}` in our examples.
      | c :: cs =>
        match charDigit c with
          | .error _ => return { text := { data := text.reverse }, tok := Tok.num soFar } :: (← lex2 (c::cs)) -- Use `c::cs` here instead of `input` because the default tactic doesn't know they are equal.
          | .ok d => lex2number (soFar * 10 + d) (c :: text) cs
end
-- `termination_by` is used to specify a well-founded relation.
termination_by
  lex2 input       => (input, 0) -- Lean is proving a termination using the instance `WellFoundedRelation (List Char × Nat)` which is just a lex-order. In the future, we should be able to guess this too.
  lex2number input => (input, 1)

#eval lex2 (m := Except LexErr) "".data
#eval lex2 (m := Except LexErr) "123".data
#eval lex2 (m := Except LexErr) "1+23".data
#eval lex2 (m := Except LexErr) "1+23()".data

-- By naming it `Option.toList`, we can use the `.` notation, and write `current.toList.map currTok`
def Option.toList : Option α -> List α
  | none   => []
  | some x => [x]

def lex3 [Monad m] [MonadExceptOf LexErr m] (current : Option (List Char × Nat)) (input : List Char) : m (List Token) := do
  let currTok := fun -- `fun | ...` is sugar for `fun x => match x with | ...`
    | (cs, n) => { text := {data := cs.reverse}, tok := Tok.num n }
  match input with
    | [] => return current.toList.map currTok
    | c :: cs =>
      let emit (tok : Token) (xs : List Token) : List Token :=
        match current with
        | none => tok :: xs
        | some numInfo => currTok numInfo :: tok :: xs;
      match c with
        | '(' => return emit { text := "(", tok := Tok.lpar } (← lex3 none cs)
        | ')' => return emit { text := ")", tok := Tok.rpar } (← lex3 none cs)
        | '+' => return emit { text := "+", tok := Tok.plus } (← lex3 none cs)
        | other =>
          match charDigit other with
            | .error _ => throw <| LexErr.unexpected other
            | .ok d => match current with
              | none => lex3 (some ([other], d)) cs
              | some (tokTxt, soFar) => lex3 (other :: tokTxt, soFar * 10 + d) cs

#eval lex3 (m := Except LexErr) none "".data
#eval lex3 (m := Except LexErr) none "123".data
#eval lex3 (m := Except LexErr) none "1+23".data
#eval lex3 (m := Except LexErr) none "1+23()".data

/- Identical to lex2, but avoiding the hack where we replace `input` with `c::cs`. -/
mutual
  def lex4 [Monad m] [MonadExceptOf LexErr m] (input : List Char) : m (List Token) := do
    match input with
      | [] => pure []
      | c :: cs =>
        match c with
          | '(' => return { text := "(", tok := Tok.lpar } :: (← lex4 cs)  -- Let's always use `return` and the nested method notation.
          | ')' => return { text := ")", tok := Tok.rpar } :: (← lex4 cs)
          | '+' => return { text := "+", tok := Tok.plus } :: (← lex4 cs)
          | other =>
            match charDigit other with
              -- Lean can infer the namespace of constructors using the expected type. `.error` here is just shorthand for `Except.error`
              | .error _ => throw <| LexErr.unexpected other -- Let's avoid `$`. We still support if for old Lean users and Haskell users, but we are now using the F# `<|`.
              | .ok d    => lex4number d [other] cs -- It was `input` here, I believe it was a typo

  def lex4number [Monad m] [MonadExceptOf LexErr m] (soFar : Nat) (text : List Char) (input : List Char) : m (List Token) :=
    match h : input with
      | [] => return [{ text := { data := text.reverse }, tok := Tok.num soFar }] -- We always use space after `{` and before `}` in our examples.
      | c :: cs =>
        match charDigit c with
          | .error _ => return { text := { data := text.reverse }, tok := Tok.num soFar } :: (← lex4 input)
          | .ok d => lex4number (soFar * 10 + d) (c :: text) cs
end
termination_by
  lex4 input       => (input, 0) -- Lean is proving a termination using the instance `WellFoundedRelation (List Char × Nat)` which is just a lex-order. In the future, we should be able to guess this too.
  lex4number input => (input, 1)
-- decreasing_by allows us to specify a tactic for showing the recursive applications are decreasing.
decreasing_by
  solve | decreasing_tactic -- get easy cases with the builtin tactic `decreasing_tactic`
        | simp_wf; simp [*]; apply Prod.Lex.right; simp_arith -- `simp [*]` is replacing `h : input = c :: cs`

#eval lex4 (m := Except LexErr) "".data
#eval lex4 (m := Except LexErr) "123".data
#eval lex4 (m := Except LexErr) "1+23".data
#eval lex4 (m := Except LexErr) "1+23()".data

inductive LexState where
  | top
  | num : Nat → List Char → LexState
  deriving Repr

-- This version doesn't work due to lack of structural recursion
-- (presumably when switching states from number back to non-number)
def lex [Monad m] [MonadExceptOf LexErr m] (state : LexState) (input : List Char) : m (List Token) :=
  match state with
    | LexState.top =>
      match h : input with
        | [] => pure []
        | c :: cs =>
          match c with
            | '(' => return { text := "(", tok := Tok.lpar } :: (← lex LexState.top cs)
            | ')' => return { text := ")", tok := Tok.rpar } :: (← lex LexState.top cs)
            | '+' => return { text := "+", tok := Tok.plus } :: (← lex LexState.top cs)
            | other =>
              match charDigit other with
                | .error _ => throw <| LexErr.unexpected other
                | .ok d => lex (LexState.num d [other]) cs
    | LexState.num soFar text =>
      match h : input with
        | [] => return [{ text := { data := text.reverse }, tok := Tok.num soFar }]
        | c :: cs =>
          match charDigit c with
            | .error _ => return { text := { data := text.reverse }, tok := Tok.num soFar } :: (← lex LexState.top input)
            | .ok d => lex (LexState.num (soFar * 10 + d) (c :: text)) cs
termination_by lex state input =>
  match state with
  | .top    => (input, 0)
  | .num .. => (input, 1)
decreasing_by
  solve | decreasing_tactic
        | simp_wf; simp [*]; apply Prod.Lex.right; simp_arith

#eval lex (m := Except LexErr) (state := .top) "".data
#eval lex (m := Except LexErr) (state := .top) "123".data
#eval lex (m := Except LexErr) (state := .top) "1+23".data
#eval lex (m := Except LexErr) (state := .top) "1+23()".data
