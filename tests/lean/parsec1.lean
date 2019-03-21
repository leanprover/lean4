import init.lean.parser.identifier
open Lean.Parser
open Lean.Parser.MonadParsec

def test {α} [DecidableEq α] (p : Parsec' α) (s : String) (e : α) : IO Unit :=
match Parsec.parse p s with
| Except.ok a    := if a = e then pure () else IO.println "unexpected Result"
| Except.error e := IO.println e

def testFailure {α} (p : Parsec' α) (s : String) : IO Unit :=
match Parsec.parse p s with
| Except.ok a    := IO.println "unexpected success"
| Except.error e := pure ()

def showResult {α} [HasToString α] (p : Parsec' α) (s : String) : IO Unit :=
match Parsec.parse p s with
| Except.ok a    := IO.println "Result: " *> IO.println (repr $ toString a)
| Except.error e := IO.println e

#exit -- Disabled until we implement new VM

#eval test (ch 'a') "a" 'a'
#eval test any "a" 'a'
#eval test any "b" 'b'
#eval test (str "foo" <|> str "bla" <|> str "boo") "bla" "bla"
#eval test ((str "foo" *> str "foo") <|> str "bla" <|> str "boo") "bla" "bla"
#eval testFailure ((str "foo" *> str "foo") <|> str "foo2" <|> str "boo") "foo2"
#eval test (try (str "foo" *> str "foo") <|> str "foo2" <|> str "boo") "foo2" "foo2"
#eval test num "1000" 1000
#eval test (do n ← num, whitespace, m ← num, pure (n, m)) "1000 200" (1000, 200)
#eval test (do n ← num, whitespace, m ← num, pure (n, m)) "1000      200" (1000, 200)
#eval test (do n ← lexeme num, m ← num, pure (n, m)) "1000 200" (1000, 200)
#eval test (whitespace *> Prod.mk <$> (lexeme num) <*> (lexeme num)) "    1000 200    " (1000, 200)
#eval test (whitespace *> Prod.mk <$> (lexeme num) <*> (lexeme num) <* eoi) "    1000 200    " (1000, 200)
#eval testFailure (whitespace *> Prod.mk <$> (lexeme num) <*> num <* eoi) "    1000 200    "

#eval testFailure ((ch 'a' *> ch 'b') <|> (ch 'a' *> ch 'c')) "ac"
#eval test ((lookahead (str "ab") *> ch 'a' *> ch 'b') <|> (ch 'a' *> ch 'c')) "ac" 'c'
#eval test (str "ab" *> pure () <|> (ch 'a' *> ch 'c' *> pure ())) "ac" ()
#eval test (try (ch 'a' *> ch 'b') <|> (ch 'a' *> ch 'c')) "ac" 'c'
#eval test (lookahead (ch 'a')) "abc" 'a'
#eval testFailure (notFollowedBy (lookahead (ch 'a'))) "abc"

def symbol (c : Char) : Parsec' Char :=
lexeme (ch c) <?> repr c

def paren {α} (p : Parsec' α) : Parsec' α :=
symbol '(' *> lexeme p <* symbol ')'

#eval test (paren num) "(   10 )" 10
#eval test (paren num) "(12)" 12
#eval test (paren num) "(0)" 0
#eval test (paren num) "(0    )" 0

def var : Parsec' String :=
do c ← satisfy (λ a, a.isAlpha || a = '_'),
   r ← lexeme $ takeWhile (λ a, a.isDigit || a.isAlpha || a = '_'),
   pure (c.toString ++ r)

#eval test var "abc" "abc"
#eval test var "_a1Bc" "_a1Bc"
#eval test (paren var) "(_a1Bc )" "_a1Bc"
#eval testFailure var "1A1Bc"
#eval testFailure var "*_a1Bc"
#eval test var "abc$" "abc"

open Lean

#eval test identifier "«!!aaa».b1'" (mkStrName (mkSimpleName "!!aaa") "b1'")
#eval test identifier "a" (mkSimpleName "a")
#eval test identifier "a'" (mkSimpleName "a'")
#eval test identifier "_" (mkSimpleName "_")
#eval test identifier "_a1" (mkSimpleName "_a1")
#eval test identifier "aaa.bbb._αc" (mkStrName (mkStrName (mkSimpleName "aaa") "bbb") "_αc")
#eval test identifier "«!a!aa».b12.ccc" (mkStrName (mkStrName (mkSimpleName "!a!aa") "b12") "ccc")
#eval testFailure identifier "1A1Bc"
#eval testFailure identifier "!"
#eval testFailure identifier "1"
#eval testFailure identifier "'a"
#eval testFailure identifier ""
#eval testFailure identifier " "

#eval test parseStringLiteral "\"abc\"" "abc"
#eval test parseStringLiteral "\"\\\\abc\"" "\\abc"
#eval test parseStringLiteral "\"\"" ""
#eval test parseStringLiteral "\"\\\"\"" "\""
#eval test parseStringLiteral "\"\\\'\"" "\'"
#eval test parseStringLiteral "\"\\n\"" "\n"
#eval test parseStringLiteral "\"\\t\"" "\t"
#eval test parseStringLiteral "\"\\x4e\"" "N"
#eval test parseStringLiteral "\"\\x4E\"" "N"
#eval test parseStringLiteral "\"\\x7D\"" "}"
#eval test parseStringLiteral "\"\\u03b1\\u03b1\"" "αα"
#eval testFailure parseStringLiteral "\"abc"
#eval testFailure parseStringLiteral "\"\\abc\""
#eval testFailure parseStringLiteral "\"\\x4z\""
#eval testFailure parseStringLiteral "\"\\x4\""
#eval testFailure parseStringLiteral "\"\\u03b\\u03b1\""
#eval testFailure parseStringLiteral "\"\\u03bz\\u03b1\""

def parseInstrPp : Parsec' String :=
do cmd ← Lean.Ir.parseInstr,
   pure $ toString cmd

#eval test parseInstrPp "x :    UInt32 :=  10" "x : UInt32 := 10"
#eval test parseInstrPp "x : Bool:=not y" "x : Bool := not y"
#eval test parseInstrPp "x : Bool := and z   y" "x : Bool := and z y"
#eval test parseInstrPp "x := call f z w" "x := call f z w"
#eval test parseInstrPp "x := call f z   w" "x := call f z w"
#eval test parseInstrPp "o := cnstr 0   3   0" "o := cnstr 0 3 0"
#eval test parseInstrPp "set o 0 x" "set o 0 x"
#eval test parseInstrPp "x := get o 0" "x := get o 0"
#eval test parseInstrPp "sset o 8 x" "sset o 8 x"
#eval test parseInstrPp "x : Bool := sget o 24" "x : Bool := sget o 24"
#eval test parseInstrPp "x := closure f a" "x := closure f a"
#eval test parseInstrPp "x := closure f a b" "x := closure f a b"
#eval test parseInstrPp "x := apply f a" "x := apply f a"
#eval test parseInstrPp "x := Array sz c" "x := Array sz c"
#eval test parseInstrPp "arrayWrite a i v" "arrayWrite a i v"
#eval test parseInstrPp "x : object := arrayRead a i" "x : object := arrayRead a i"
#eval test parseInstrPp "x := sarray UInt32 sz c" "x := sarray UInt32 sz c"
#eval test parseInstrPp "arrayWrite a i v" "arrayWrite a i v"
#eval test parseInstrPp "x : UInt64 := arrayRead a i" "x : UInt64 := arrayRead a i"
#eval test parseInstrPp "inc x" "inc x"
#eval test parseInstrPp "dec x" "dec x"
#eval test parseInstrPp "decSref x" "decSref x"
#eval test parseInstrPp "free x" "free x"
#eval test parseInstrPp "x := call  f" "x := call f"
#eval test parseInstrPp "x:UInt32:=   arrayRead y   z" "x : UInt32 := arrayRead y z"

inductive Expr
| Add : Expr → Expr → Expr
| Num : Nat → Expr
| Var : String → Expr

open Expr

def eqExpr : Π a b : Expr, Decidable (a = b)
| (Var x)     (Var y)     := if h : x = y then isTrue (h ▸ rfl)
                             else isFalse (λ h', Expr.noConfusion h' (λ h', absurd h' h))
| (Var x)     (Num n)     := isFalse (λ h, Expr.noConfusion h)
| (Var x)     (Add e₁ e₂) := isFalse (λ h, Expr.noConfusion h)
| (Num n)     (Num m)     := if h : n = m then isTrue (h ▸ rfl)
                             else isFalse (λ h', Expr.noConfusion h' (λ h', absurd h' h))
| (Num n)     (Var y)     := isFalse (λ h, Expr.noConfusion h)
| (Num n)     (Add e₁ e₂) := isFalse (λ h, Expr.noConfusion h)
| (Add e₁ e₂) (Num n)     := isFalse (λ h, Expr.noConfusion h)
| (Add e₁ e₂) (Var y)     := isFalse (λ h, Expr.noConfusion h)
| (Add e₁ e₂) (Add e₃ e₄) :=
  match eqExpr e₁ e₃ with
  | isTrue h   := (match eqExpr e₂ e₄ with
                    | isTrue  h' := isTrue (h ▸ h' ▸ rfl)
                    | isFalse h' := isFalse (λ he, Expr.noConfusion he (λ h₁ h₂, absurd h₂ h')))
  | isFalse h := isFalse (λ he, Expr.noConfusion he (λ h₁ h₂, absurd h₁ h))

instance : DecidableEq Expr :=
{decEq := eqExpr}

def parseAtom (p : Parsec' Expr) : Parsec' Expr :=
(Var <$> lexeme var <?> "variable")
<|>
(Num <$> lexeme num <?> "numeral")
<|>
(paren p)

def parseAdd (p : Parsec' Expr) : Parsec' Expr :=
do l ← parseAtom p,
   (do symbol '+', r ← p, pure $ Add l r) <|> pure l

def parseExpr : Parsec' Expr :=
whitespace *> fix (λ F, parseAdd F) <* eoi

#eval test parseExpr "10" (Num 10)
#eval test parseExpr "(20)" (Num 20)
#eval test parseExpr "a" (Var "a")
#eval test parseExpr "(20 + a)" (Add (Num 20) (Var "a"))
#eval test parseExpr "  (20 + (a) + 2 ) " (Add (Num 20) (Add (Var "a") (Num 2)))

/- Failures -/
#print "Failure 1"
#eval test parseExpr "(20 +" (Num 0)
#print "---------"
#print "Failure 2"
#eval test parseExpr ""      (Num 0)
#print "---------"

namespace paperEx
#print "Failure 3"
def digit  : Parsec' Char := MonadParsec.digit <?> "digit"
def letter : Parsec' Char := MonadParsec.alpha <?> "letter"
def tst    : Parsec' Char := (digit <|> pure '0') *> letter
#eval test tst "*" 'a'
#print "---------"
end paperEx
