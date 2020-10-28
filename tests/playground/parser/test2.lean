import parser

abbrev Parser (α : Type) := Lean.Parser.ParserM Unit Unit Unit α

open Lean.Parser

def check {α} [BEq α] (p : Parser α) (s : String) (e : α) : IO Unit :=
match p.run () () s with
| Lean.Parser.Result.ok v i _ _  := do
  IO.println ("Ok at " ++ toString i),
  unless (v == e) (throw "unexpected result")
| Result.error msg _ _ _         := throw msg

def checkFailure {α} (p : Parser α) (s : String) : IO Unit :=
match p.run () () s with
| Lean.Parser.Result.ok _ i _ _  := throw "Worked"
| Result.error msg i _ _         := IO.println ("failed as expected at " ++ toString i ++ ", error: " ++ toString msg)

def str' (s : String) : Parser String :=
str s *> pure s

def main : IO Unit :=
do check (ch 'a') "a" 'a',
   check any "a" 'a',
   check any "b" 'b',
   check (str' "foo" <|> str' "bla" <|> str' "boo") "bla" "bla",
   check (try (str' "foo" *> str' "foo") <|> str' "foo2" <|> str' "boo") "foo2" "foo2",
   checkFailure ((str' "foo" *> str' "abc") <|> str' "foo2" <|> str' "boo") "foo2",
   check (str' "foofoo" <|> str' "foo2" <|> str' "boo") "foo2" "foo2",
   check (leanWhitespace *> str' "hello") "   \n-- comment\nhello" "hello",
   check (takeUntil (== '\n') *> ch '\n' *> str' "test") "\ntest" "test",
   check (takeUntil (== 't') *> str' "test") "test" "test",
   check (takeUntil (== '\n') *> ch '\n' *> str' "test") "abc\ntest" "test",
   check (try (ch 'a' *> ch 'b') <|> (ch 'a' *> ch 'c')) "ac" 'c',
   checkFailure ((ch 'a' *> ch 'b') <|> (ch 'a' *> ch 'c')) "ac",
   check (lookahead (ch 'a')) "abc" 'a',
   check (lookahead (ch 'a') *> str' "abc") "abc" "abc",
   check strLit "\"abc\\nd\"" "abc\nd",
   checkFailure strLit "abc\\nd\"",
   checkFailure strLit "\"abc",
   checkFailure strLit "\"abc\\ab̈\""
