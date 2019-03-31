namespace Lean
namespace Parser

abbrev Pos := String.Pos

/-
σ  is the non-backtrackable State
δ  is the backtrackable State
μ  is the extra error Message data
-/
inductive Result (σ δ μ α : Type)
| ok    {} (a : α)        (i : Pos) (st : σ) (bst : δ)          : Result
| error {} (msg : String) (i : Pos) (st : σ) (extra : Option μ) : Result

inductive Result.IsOk {σ δ μ α : Type} : Result σ δ μ α → Prop
| mk (a : α) (i : Pos) (st : σ) (bst : δ) : Result.IsOk (Result.ok a i st bst)

theorem errorIsNotOk {σ δ μ α : Type} {msg : String} {i : Pos} {st : σ} {extra : Option μ}
                     (h : Result.IsOk (@Result.error σ δ μ α msg i st extra)) : False :=
match h with end

@[inline] def unreachableError {σ δ μ α β : Type} {msg : String} {i : Pos} {st : σ} {extra : Option μ}
                               (h : Result.IsOk (@Result.error σ δ μ α msg i st extra)) : β :=
False.elim (errorIsNotOk h)

def input (σ δ μ : Type) : Type := { r : Result σ δ μ Unit // r.IsOk }

@[inline] def mkInput {σ δ μ : Type} (i : Pos) (st : σ) (bst : δ) : input σ δ μ :=
⟨Result.ok () i st bst, Result.IsOk.mk _ _ _ _⟩

def ParserM (σ δ μ α : Type) :=
String → input σ δ μ → Result σ δ μ α

variables {σ δ μ α β : Type}

namespace ParserM

protected def default : ParserM σ δ μ α :=
λ _ inp,
  match inp with
  | ⟨Result.ok _ i st bst, h⟩ := Result.error "" i st none
  | ⟨Result.error _ _ _ _, h⟩ := unreachableError h

instance : Inhabited (ParserM σ δ μ α) :=
⟨ParserM.default⟩

@[inline] def run (p : ParserM σ δ μ α) (st : σ) (bst : δ) (s : String) : Result σ δ μ α :=
p s (mkInput 0 st bst)

@[inline] def pure (a : α) : ParserM σ δ μ α :=
λ _ inp,
  match inp with
  | ⟨Result.ok _ it st bst, h⟩ := Result.ok a it st bst
  | ⟨Result.error _ _ _ _, h⟩  := unreachableError h

@[inline] def bind (x : ParserM σ δ μ α) (f : α → ParserM σ δ μ β) : ParserM σ δ μ β :=
λ str inp,
  match x str inp with
  | Result.ok a i st bst      := f a str (mkInput i st bst)
  | Result.error msg i st etx := Result.error msg i st etx

instance isMonad : Monad (ParserM σ δ μ) :=
{pure := @ParserM.pure _ _ _, bind := @ParserM.bind _ _ _}

def mkError (r : input σ δ μ) (msg : String) : Result σ δ μ α :=
match r with
| ⟨Result.ok _ i st _, _⟩   := Result.error msg i st none
| ⟨Result.error _ _ _ _, h⟩ := unreachableError h

@[inline] def orelse (p q : ParserM σ δ μ α) : ParserM σ δ μ α :=
λ str inp,
  match inp with
  | ⟨Result.ok _ i₁ _ bst₁, _⟩ :=
    (match p str inp with
     | err@(Result.error _ i₂ st₂ _) := if i₁ == i₂ then q str (mkInput i₁ st₂ bst₁) else err
     | other                         := other)
  | ⟨Result.error _ _ _ _, h⟩ := unreachableError h

@[inline] def failure : ParserM σ δ μ α :=
λ _ inp, mkError inp "failure"

instance : Alternative (ParserM σ δ μ) :=
{ orelse         := @ParserM.orelse _ _ _,
  failure        := @ParserM.failure _ _ _,
  .. ParserM.isMonad }

@[inline] def currPos : input σ δ μ → Pos
| ⟨Result.ok _ i _ _, _⟩    := i
| ⟨Result.error _ _ _ _, h⟩ := unreachableError h

@[inline] def try {α : Type} (p : ParserM σ δ μ α) : ParserM σ δ μ α :=
λ str inp,
  match inp with
  | ⟨Result.ok _ i _ _, _⟩    := (match p str inp with
    | Result.error msg _ st x := Result.error msg i st x
    | other                   := other)
  | ⟨Result.error _ _ _ _, h⟩ := unreachableError h

@[inline] def lookahead (p : ParserM σ δ μ α) : ParserM σ δ μ α :=
λ str inp,
  match inp with
  | ⟨Result.ok _ i _ bst, _⟩ :=
    (match p str inp with
     | Result.ok a _ st _ := Result.ok a i st bst
     | other              := other)
  | ⟨Result.error _ _ _ _, h⟩ := unreachableError h

@[specialize] def satisfy (p : Char → Bool) : ParserM σ δ μ Char :=
λ str inp,
  match inp with
  | ⟨Result.ok _ i st bst, _⟩ :=
    if str.atEnd i then mkError inp "end of input"
    else let c := str.get i in
         if p c then Result.ok c (str.next i) st bst
         else mkError inp "unexpected character"
  | ⟨Result.error _ _ _ _, h⟩ := unreachableError h

@[inline] def ch (c : Char) : ParserM σ δ μ Char :=
satisfy (== c)

@[inline] def any : ParserM σ δ μ Char :=
satisfy (λ _, true)

@[specialize] partial def takeUntilAux (p : Char → Bool) : ParserM σ δ μ Unit
| str inp :=
  match inp with
  | ⟨Result.ok _ i st bst, _⟩ :=
    if str.atEnd i then inp.val
    else let c := str.get i in
         if p c then inp.val
         else takeUntilAux str (mkInput (str.next i) st bst)
  | ⟨Result.error _ _ _ _, h⟩ := unreachableError h

@[inline] def takeUntil (p : Char → Bool) : ParserM σ δ μ Unit :=
λ str inp, takeUntilAux p str inp

partial def strAux (s : String) (errorMsg : String) : Pos → ParserM σ δ μ Unit
| j str inp :=
  if s.atEnd j then inp.val
  else match inp with
    | ⟨Result.ok _ i st bst, _⟩ :=
      if str.atEnd i then mkError inp errorMsg
      else if s.get j == str.get i then strAux (s.next j) str (mkInput (str.next i) st bst)
      else mkError inp errorMsg
    | ⟨Result.error _ _ _ _, h⟩ := unreachableError h

@[inline] def str (s : String) : ParserM σ δ μ Unit :=
strAux s ("expected '" ++ repr s ++ "'") 0

@[specialize] partial def manyAux (a : α) (p : ParserM σ δ μ α) : ParserM σ δ μ α
| str inp :=
  match inp with
  | ⟨Result.ok _ i₀ _ bst₀, _⟩ :=
    (match p str inp with
     | Result.ok _ i st bst   := manyAux str (mkInput i st bst)
     | Result.error _ _ st _  := Result.ok a i₀ st bst₀)
  | ⟨Result.error _ _ _ _, h⟩ := unreachableError h

@[inline] def many (p : ParserM σ δ μ Unit) : ParserM σ δ μ Unit  :=
manyAux () p

@[inline] def many1 (p : ParserM σ δ μ Unit) : ParserM σ δ μ Unit  :=
p *> many p

def pos : ParserM σ δ μ Pos :=
λ str inp,
  match inp with
  | ⟨Result.ok _ i st bst, _⟩ := Result.ok i i st bst
  | ⟨Result.error _ _ _ _, h⟩ := unreachableError h

def error {α : Type} (msg : String) : ParserM σ δ μ α :=
λ _ inp, mkError inp msg

def errorAt {α : Type} (pos : Pos) (msg : String) : ParserM σ δ μ α :=
λ _ inp, match inp with
| ⟨Result.ok _ _ st _, _⟩   := Result.error msg pos st none
| ⟨Result.error _ _ _ _, h⟩ := unreachableError h

def hexDigit : ParserM σ δ μ Nat
| str inp := match inp with
  | ⟨Result.ok _ i st bst, _⟩ :=
    if str.atEnd i then mkError inp "unexpected end of input"
    else
      let c := str.get i in
      let i := str.next i in
      if c.isDigit then Result.ok (c.toNat - '0'.toNat) i st bst
      else if 'a' <= c && c <= 'f' then Result.ok (10 + c.toNat - 'a'.toNat) i st bst
      else if 'A' <= c && c <= 'F' then Result.ok (10 + c.toNat - 'A'.toNat) i st bst
      else mkError inp "invalid hexadecimal numeral, hexadecimal digit expected"
  | ⟨Result.error _ _ _ _, h⟩ := unreachableError h

def quotedChar : ParserM σ δ μ Char :=
do p ← pos,
   c ← any,
   if c = '\\'      then pure '\\'
   else if c = '\"' then pure '\"'
   else if c = '\'' then pure '\''
   else if c = 'n'  then pure '\n'
   else if c = 't'  then pure '\t'
   else if c = 'x'  then do {
     d₁ ← hexDigit,
     d₂ ← hexDigit,
     pure $ Char.ofNat (16*d₁ + d₂) }
   else if c = 'u'  then do {
     d₁ ← hexDigit,
     d₂ ← hexDigit,
     d₃ ← hexDigit,
     d₄ ← hexDigit,
     pure $ Char.ofNat (16*(16*(16*d₁ + d₂) + d₃) + d₄) }
   else errorAt p "invalid escape sequence"

partial def strLitAux : String → ParserM σ δ μ String
| out := do
  c ← any,
  if c == '\"' then pure out
  else if c == '\\' then do c ← quotedChar, strLitAux (out.push c)
  else strLitAux (out.push c)

def strLit : ParserM σ δ μ String :=
ch '\"' *> strLitAux ""

partial def finishCommentBlock : Nat → ParserM σ δ μ Unit
| nesting str inp :=
  match inp with
  | ⟨Result.ok _ i st bst, _⟩ :=
    if str.atEnd i then mkError inp "end of input"
    else
      let c := str.get i in
      let i := str.next i in
      if c == '-' then
        if str.atEnd i then mkError inp "end of input"
        else
          let c := str.get i in
          if c == '/' then -- "-/" end of comment
            if nesting == 1 then Result.ok () (str.next i) st bst
            else finishCommentBlock (nesting-1) str (mkInput (str.next i) st bst)
          else
            finishCommentBlock nesting str (mkInput i st bst)
      else if c == '/' then
        if str.atEnd i then mkError inp "end of input"
        else
          let c := str.get i in
          if c == '-' then finishCommentBlock (nesting+1) str (mkInput (str.next i) st bst)
          else finishCommentBlock nesting str (mkInput i st bst)
      else finishCommentBlock nesting str (mkInput i st bst)
  | ⟨Result.error _ _ _ _, h⟩ := unreachableError h

partial def leanWhitespace : ParserM σ δ μ Unit
| str inp :=
  match inp with
  | ⟨Result.ok _ i st bst, _⟩ :=
    if str.atEnd i then inp.val
    else
      let c := str.get i in
      if c.isWhitespace then leanWhitespace str (mkInput (str.next i) st bst)
      else if c == '-' then
        let i := str.next i in
        let c := str.get i in
        if c == '-' then ((takeUntil (= '\n')) *> leanWhitespace) str (mkInput i st bst)
        else inp.val
      else if c == '/' then
        let i := str.next i in
        let c := str.get i in
        if c == '-' then
          let i := str.next i in
          let c := str.get i in
          if c == '-' then inp.val -- "/--" doc comment is an actual token
          else ((finishCommentBlock 1) *> leanWhitespace) str (mkInput i st bst)
        else inp.val
      else inp.val
  | ⟨Result.error _ _ _ _, h⟩ := unreachableError h

end ParserM

class monadParser (σ : outParam Type) (δ : outParam Type) (μ : outParam Type) (m : Type → Type) :=
(lift {} {α : Type} : ParserM σ δ μ α → m α)
(map {} {α : Type} : (Π β, ParserM σ δ μ β → ParserM σ δ μ β) → m α → m α)

instance monadParserBase : monadParser σ δ μ (ParserM σ δ μ) :=
{ lift := λ α, id,
  map  := λ α f x, f α x }

instance monadParserTrans {m n : Type → Type} [HasMonadLift m n] [MonadFunctor m m n n] [monadParser σ δ μ m] : monadParser σ δ μ n :=
{ lift := λ α p, monadLift (monadParser.lift p : m α),
  map  := λ α f x, monadMap (λ β x, (monadParser.map @f x : m β)) x }

class monadParserAux (σ : outParam Type) (δ : outParam Type) (μ : outParam Type) (m : Type → Type) :=
(map {} {α : Type} : (ParserM σ δ μ α → ParserM σ δ μ α) → m α → m α)

instance monadParserAuxBase : monadParserAux σ δ μ (ParserM σ δ μ) :=
{ map  := λ α, id }

instance monadParserAuxReader {m : Type → Type} {ρ : Type} [Monad m] [monadParserAux σ δ μ m] : monadParserAux σ δ μ (ReaderT ρ m) :=
{ map  := λ α f x r, (monadParserAux.map f : m α → m α) (x r) }

section
variables {m : Type → Type} [monadParser σ δ μ m]

@[inline] def satisfy (p : Char → Bool) : m Char := monadParser.lift (ParserM.satisfy p)
def ch (c : Char) : m Char := satisfy (== c)
def alpha : m Char := satisfy Char.isAlpha
def digit : m Char := satisfy Char.isDigit
def upper : m Char := satisfy Char.isUpper
def lower : m Char := satisfy Char.isLower
def any   : m Char := satisfy (λ _, true)

@[inline] def takeUntil (p : Char → Bool) : m Unit := monadParser.lift (ParserM.takeUntil p)

@[inline] def str (s : String) : m Unit := monadParser.lift (ParserM.str s)

@[inline] def lookahead (p : m α) : m α :=
monadParser.map (λ β p, ParserM.lookahead p) p

@[inline] def takeWhile (p : Char → Bool) : m Unit := takeUntil (λ c, !p c)

@[inline] def whitespace : m Unit := takeWhile Char.isWhitespace

@[inline] def strLit : m String := monadParser.lift (ParserM.strLit)

@[inline] def leanWhitespace : m Unit := monadParser.lift ParserM.leanWhitespace
end

section
variables {m : Type → Type} [monadParserAux σ δ μ m]

@[inline] def many (p : m Unit) : m Unit  := monadParserAux.map ParserM.many p
@[inline] def many1 (p : m Unit) : m Unit := monadParserAux.map ParserM.many1 p

end

end Parser
end Lean

abbrev Parser (α : Type) := ReaderT Nat (Lean.Parser.ParserM Unit Unit Unit) α

open Lean.Parser

-- setOption pp.implicit True
-- setOption Trace.Compiler.boxed True

def testP : Parser Unit :=
many1 (str "++" <|> str "**" <|> (str "--" *> takeUntil (= '\n') *> any *> pure ()))

def testP2 : Parser Unit :=
many1 ((strLit *> whitespace *> pure ()) <|> (str "--" *> takeUntil (= '\n') *> any *> pure ()))

def testP3 : Parser Unit :=
leanWhitespace

def testParser (x : Parser Unit) (input : String) : String :=
match (x 0).run () () input with
| Lean.Parser.Result.ok _ i _ _  := "Ok at " ++ toString i
| Result.error msg i _ _         := "Error at " ++ toString i ++ ": " ++ msg

def IO.testParser {α : Type} [HasToString α] (x : Parser α) (input : String) : IO Unit :=
match (x 0).run () () input with
| Lean.Parser.Result.ok a _ _ _  := IO.println ("Ok " ++ toString a)
| _                              := throw "ERROR"

@[noinline] def test (p : Parser Unit) (s : String) : IO Unit :=
IO.println (testParser p s)

def mkBigString : Nat → String → String
| 0     s := s
| (n+1) s := mkBigString n (s ++ "-- new comment\n")

def mkBigString2 : Nat → String → String
| 0     s := s
| (n+1) s := mkBigString2 n (s ++ "\"hello\\nworld\"\n-- comment\n")

def mkBigString3 : Nat → String → String
| 0     s := s
| (n+1) s := mkBigString3 n (s ++ "/- /- comment 1 -/ -/ \n -- comment 2 \n \t \n ")

def prof {α : Type} (msg : String) (p : IO α) : IO α :=
let msg₁ := "Time for '" ++ msg ++ "':" in
let msg₂ := "Memory usage for '" ++ msg ++ "':" in
allocprof msg₂ (timeit msg₁ p)

def tst1 : IO Unit :=
IO.testParser strLit "\"hello\n\""

def main (xs : List String) : IO Unit :=
do
tst1,
let s₁ := mkBigString xs.head.toNat "",
let s₂ := s₁ ++ "bad" ++ mkBigString 20 "",
let s₃ := mkBigString2 xs.head.toNat "",
let s₄ := mkBigString3 xs.head.toNat "",
IO.println s₄.length,
prof "Parser 1" (test testP s₁),
prof "Parser 2" (test testP s₂),
prof "Parser 3" (test testP2 s₃),
prof "Parser 4" (test testP3 s₄)
