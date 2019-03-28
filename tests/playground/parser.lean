namespace Lean
namespace Parser

abbrev Pos := String.Pos

/-
σ  is the non-backtrackable State
δ  is the backtrackable State
μ  is the extra error Message data
-/
inductive Result (σ δ μ α : Type)
| ok    {} (a : α)        (i : Pos) (st : σ) (bst : δ)          (eps : Bool) : Result
| error {} (msg : String) (i : Pos) (st : σ) (extra : Option μ) (eps : Bool) : Result

inductive Result.IsOk {σ δ μ α : Type} : Result σ δ μ α → Prop
| mk (a : α) (i : Pos) (st : σ) (bst : δ) (eps : Bool) : Result.IsOk (Result.ok a i st bst eps)

theorem errorIsNotOk {σ δ μ α : Type} {msg : String} {i : Pos} {st : σ} {extra : Option μ} {eps : Bool}
                     (h : Result.IsOk (@Result.error σ δ μ α msg i st extra eps)) : False :=
match h with end

@[inline] def unreachableError {σ δ μ α β : Type} {msg : String} {i : Pos} {st : σ} {extra : Option μ} {eps : Bool}
                                (h : Result.IsOk (@Result.error σ δ μ α msg i st extra eps)) : β :=
False.elim (errorIsNotOk h)

def input (σ δ μ : Type) : Type := { r : Result σ δ μ Unit // r.IsOk }

@[inline] def mkInput {σ δ μ : Type} (i : Pos) (st : σ) (bst : δ) (eps := true) : input σ δ μ :=
⟨Result.ok () i st bst eps, Result.IsOk.mk _ _ _ _ _⟩

def parserM (σ δ μ α : Type) :=
String → input σ δ μ → Result σ δ μ α

variables {σ δ μ α β : Type}

@[inline] def parserM.run (p : parserM σ δ μ α) (st : σ) (bst : δ) (s : String) : Result σ δ μ α :=
p s (mkInput 0 st bst)

@[inline] def parserM.pure (a : α) : parserM σ δ μ α :=
λ _ inp,
  match inp with
  | ⟨Result.ok _ it st bst _, h⟩ := Result.ok a it st bst true
  | ⟨Result.error _ _ _ _ _, h⟩  := unreachableError h

@[inline] def parserM.bind (x : parserM σ δ μ α) (f : α → parserM σ δ μ β) : parserM σ δ μ β :=
λ str inp,
  match x str inp with
  | Result.ok a i st bst e₁ :=
    (match f a str (mkInput i st bst) with
     | Result.ok b i st bst e₂      := Result.ok b i st bst (strictAnd e₁ e₂)
     | Result.error msg i st ext e₂ := Result.error msg i st ext (strictAnd e₁ e₂))
  | Result.error msg i st etx e  := Result.error msg i st etx e

instance parserMIsMonad : Monad (parserM σ δ μ) :=
{pure := @parserM.pure _ _ _, bind := @parserM.bind _ _ _}

def mkError (r : input σ δ μ) (msg : String) (eps := true) : Result σ δ μ α :=
match r with
| ⟨Result.ok _ i c s _, _⟩    := Result.error msg i c none eps
| ⟨Result.error _ _ _ _ _, h⟩ := unreachableError h

@[inline] def parserM.orelse (p q : parserM σ δ μ α) : parserM σ δ μ α :=
λ str inp,
  match inp with
  | ⟨Result.ok _ i₁ _ bst₁ _, _⟩ :=
    (match p str inp with
     | Result.error _ _ st₂ _ tt := q str (mkInput i₁ st₂ bst₁)
     | other                     := other)
  | ⟨Result.error _ _ _ _ _, h⟩ := unreachableError h

@[inline] def parserM.failure : parserM σ δ μ α :=
λ _ inp, mkError inp "failure"

instance : Alternative (parserM σ δ μ) :=
{ orelse         := @parserM.orelse _ _ _,
  failure        := @parserM.failure _ _ _,
  .. Parser.parserMIsMonad }

def setSilentError : Result σ δ μ α → Result σ δ μ α
| (Result.error msg i st ext _) := Result.error msg i st ext true
| other                         := other

@[inline] def currPos : input σ δ μ → Pos
| ⟨Result.ok _ i _ _ _, _⟩    := i
| ⟨Result.error _ _ _ _ _, h⟩ := unreachableError h

namespace Prim
@[inline] def try {α : Type} (p : parserM σ δ μ α) : parserM σ δ μ α :=
λ str inp, setSilentError (p str inp)

@[inline] def lookahead (p : parserM σ δ μ α) : parserM σ δ μ α :=
λ str inp,
  match inp with
  | ⟨Result.ok _ i _ bst _, _⟩ :=
    (match p str inp with
     | Result.ok a _ st _ _ := Result.ok a i st bst true
     | other                := other)
  | ⟨Result.error _ _ _ _ _, h⟩ := unreachableError h

@[specialize] def satisfy (p : Char → Bool) : parserM σ δ μ Char :=
λ str inp,
  match inp with
  | ⟨Result.ok _ i st bst _, _⟩ :=
    if str.atEnd i then mkError inp "end of input"
    else let c := str.get i in
         if p c then Result.ok c (str.next i) st bst false
         else mkError inp "unexpected character"
  | ⟨Result.error _ _ _ _ _, h⟩ := unreachableError h

@[specialize] def takeUntilAux (p : Char → Bool) : Nat → parserM σ δ μ Unit
| 0     str inp := inp.val
| (n+1) str inp :=
  match inp with
  | ⟨Result.ok _ i st bst _, _⟩ :=
    if str.atEnd i then inp.val
    else let c := str.get i in
         if p c then inp.val
         else takeUntilAux n str (mkInput (str.next i) st bst false)
  | ⟨Result.error _ _ _ _ _, h⟩ := unreachableError h

@[inline] def takeUntil (p : Char → Bool) : parserM σ δ μ Unit :=
λ str inp, takeUntilAux p str.length str inp

def strAux (inS : String) (s : String) (errorMsg : String) : Nat → input σ δ μ → Pos → Result σ δ μ Unit
| 0     inp j := mkError inp errorMsg
| (n+1) inp j :=
  if s.atEnd j then inp.val
  else
    match inp with
    | ⟨Result.ok _ i st bst e, _⟩ :=
      if inS.atEnd i then mkError inp errorMsg
      else if inS.get i = s.get j then strAux n (mkInput (inS.next i) st bst false) (s.next j)
      else mkError inp errorMsg
    | ⟨Result.error _ _ _ _ _, h⟩ := unreachableError h

@[inline] def str (s : String) : parserM σ δ μ Unit :=
λ inStr inp, strAux inStr s ("expected '" ++ repr s ++ "'") inStr.length inp 0

@[specialize] def manyLoop (a : α) (p : parserM σ δ μ α) : Nat → Bool → parserM σ δ μ α
| 0     fst := pure a
| (k+1) fst := λ str inp,
  match inp with
  | ⟨Result.ok _ i₀ _ bst₀ _, _⟩ :=
    (match p str inp with
     | Result.ok _ i st bst _   := manyLoop k false str (mkInput i st bst)
     | Result.error _ _ st _ _  := Result.ok a i₀ st bst₀ fst)
  | ⟨Result.error _ _ _ _ _, h⟩ := unreachableError h

-- Auxiliary Function used to lift manyAux
@[inline] def manyAux (a : α) (p : parserM σ δ μ α) : parserM σ δ μ α :=
λ str inp, manyLoop a p str.length true str inp

@[inline] def many (p : parserM σ δ μ Unit) : parserM σ δ μ Unit  :=
manyAux () p

@[inline] def many1 (p : parserM σ δ μ Unit) : parserM σ δ μ Unit  :=
p *> many p

end Prim

class monadParser (σ : outParam Type) (δ : outParam Type) (μ : outParam Type) (m : Type → Type) :=
(lift {} {α : Type} : parserM σ δ μ α → m α)
(map {} {α : Type} : (Π β, parserM σ δ μ β → parserM σ δ μ β) → m α → m α)

instance monadParserBase : monadParser σ δ μ (parserM σ δ μ) :=
{ lift := λ α, id,
  map  := λ α f x, f α x }

instance monadParserTrans {m n : Type → Type} [HasMonadLift m n] [MonadFunctor m m n n] [monadParser σ δ μ m] : monadParser σ δ μ n :=
{ lift := λ α p, monadLift (monadParser.lift p : m α),
  map  := λ α f x, monadMap (λ β x, (monadParser.map @f x : m β)) x }

class monadParserAux (σ : outParam Type) (δ : outParam Type) (μ : outParam Type) (m : Type → Type) :=
(map {} {α : Type} : (parserM σ δ μ α → parserM σ δ μ α) → m α → m α)

instance monadParserAuxBase : monadParserAux σ δ μ (parserM σ δ μ) :=
{ map  := λ α, id }

instance monadParserAuxReader {m : Type → Type} {ρ : Type} [Monad m] [monadParserAux σ δ μ m] : monadParserAux σ δ μ (ReaderT ρ m) :=
{ map  := λ α f x r, (monadParserAux.map f : m α → m α) (x r) }

section
variables {m : Type → Type} [monadParser σ δ μ m]

@[inline] def satisfy (p : Char → Bool) : m Char := monadParser.lift (Prim.satisfy p)
def ch (c : Char) : m Char := satisfy (= c)
def alpha : m Char := satisfy Char.isAlpha
def digit : m Char := satisfy Char.isDigit
def upper : m Char := satisfy Char.isUpper
def lower : m Char := satisfy Char.isLower
def any   : m Char := satisfy (λ _, True)

@[inline] def takeUntil (p : Char → Bool) : m Unit := monadParser.lift (Prim.takeUntil p)

@[inline] def str (s : String) : m Unit := monadParser.lift (Prim.str s)

@[inline] def lookahead (p : m α) : m α :=
monadParser.map (λ β p, Prim.lookahead p) p

@[inline] def takeWhile (p : Char → Bool) : m Unit := takeUntil (λ c, !p c)

@[inline] def whitespace : m Unit := takeWhile Char.isWhitespace

end

section
variables {m : Type → Type} [monadParserAux σ δ μ m]

@[inline] def many (p : m Unit) : m Unit  := monadParserAux.map Prim.many p
@[inline] def many1 (p : m Unit) : m Unit := monadParserAux.map Prim.many1 p

end

end Parser
end Lean

abbrev Parser := ReaderT Nat (Lean.Parser.parserM Unit Unit Unit) Unit

open Lean.Parser

-- setOption pp.implicit True
-- setOption Trace.Compiler.boxed True

def testP : Parser :=
many1 (str "++" <|> str "**" <|> (str "--" *> takeUntil (= '\n') *> any *> pure ()))

def testParser (x : Parser) (input : String) : String :=
match (x 0).run () () input with
| Lean.Parser.Result.ok _ i _ _ _      := "Ok at " ++ toString i
| Result.error msg i _ _ _ := "Error at " ++ toString i ++ ": " ++ msg

@[noinline] def test (s : String) : IO Unit :=
IO.println (testParser testP s)

def mkBigString : Nat → String → String
| 0     s := s
| (n+1) s := mkBigString n (s ++ "-- new comment\n")

def prof {α : Type} (msg : String) (p : IO α) : IO α :=
let msg₁ := "Time for '" ++ msg ++ "':" in
let msg₂ := "Memory usage for '" ++ msg ++ "':" in
allocprof msg₂ (timeit msg₁ p)

def main (xs : List String) : IO Unit :=
let s₁ := mkBigString xs.head.toNat "" in
let s₂ := s₁ ++ "bad" ++ mkBigString 20 "" in
prof "Parser 1" (test s₁) *>
prof "Parser 2" (test s₂)
