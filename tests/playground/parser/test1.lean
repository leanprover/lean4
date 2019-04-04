import parser

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

def main (xs : List String) : IO Unit :=
do
let s₁ := mkBigString xs.head.toNat "",
let s₂ := s₁ ++ "bad" ++ mkBigString 20 "",
let s₃ := mkBigString2 xs.head.toNat "",
let s₄ := mkBigString3 xs.head.toNat "",
IO.println s₄.length,
prof "Parser 1" (test testP s₁),
prof "Parser 2" (test testP s₂),
prof "Parser 3" (test testP2 s₃),
prof "Parser 4" (test testP3 s₄)
