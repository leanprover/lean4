import system.io init.lean.parser.parser
open lean.parser

def test {α} [decidable_eq α] (p : parser α) (s : string) (e : α) : io unit :=
match parse p s with
| except.ok a := if a = e then return () else io.print_ln "unexpected result"
| except.error e := io.print_ln (e.to_string s)
end

def test_failure {α} (p : parser α) (s : string) : io unit :=
match parse p s with
| except.ok a    := io.print_ln "unexpected success"
| except.error e := return ()
end

#eval test (ch 'a') "a" 'a'
#eval test any "a" 'a'
#eval test any "b" 'b'
#eval test (str "foo" <|> str "bla" <|> str "boo") "bla" "bla"
#eval test ((str "foo" >> str "foo") <|> str "bla" <|> str "boo") "bla" "bla"
#eval test_failure ((str "foo" >> str "foo") <|> str "foo2" <|> str "boo") "foo2"
#eval test (try (str "foo" >> str "foo") <|> str "foo2" <|> str "boo") "foo2" "foo2"
#eval test num "1000" 1000
#eval test (do n ← num, whitespace, m ← num, return (n, m)) "1000 200" (1000, 200)
#eval test (do n ← num, whitespace, m ← num, return (n, m)) "1000      200" (1000, 200)
#eval test (do n ← lexeme num, m ← num, return (n, m)) "1000 200" (1000, 200)
#eval test (whitespace >> prod.mk <$> (lexeme num) <*> (lexeme num)) "    1000 200    " (1000, 200)
#eval test (whitespace >> prod.mk <$> (lexeme num) <*> (lexeme num) <* eoi) "    1000 200    " (1000, 200)
#eval test_failure (whitespace >> prod.mk <$> (lexeme num) <*> num <* eoi) "    1000 200    "

#eval test_failure ((ch 'a' >> ch 'b') <|> (ch 'a' >> ch 'c')) "ac"
#eval test ((lookahead (str "ab") >> ch 'a' >> ch 'b') <|> (ch 'a' >> ch 'c')) "ac" 'c'
#eval test (str "ab" >> eps <|> (ch 'a' >> ch 'c' >> eps)) "ac" ()
#eval test (try (ch 'a' >> ch 'b') <|> (ch 'a' >> ch 'c')) "ac" 'c'

def symbol (c : char) : parser char :=
lexeme (ch c) <?> repr c

def paren {α} (p : parser α) : parser α :=
symbol '(' >> lexeme p <* symbol ')'

#eval test (paren num) "(   10 )" 10
#eval test (paren num) "(12)" 12
#eval test (paren num) "(0)" 0
#eval test (paren num) "(0    )" 0

def var : parser string :=
do c ← satisfy (λ a, a.is_alpha || a = '_'),
   r ← lexeme $ take_while (λ a, a.is_digit || a.is_alpha || a = '_'),
   return (c.to_string ++ r)

#eval test var "abc" "abc"
#eval test var "_a_1bc" "_a_1bc"
#eval test (paren var) "(_a_1bc )" "_a_1bc"
#eval test_failure var "1_a_1bc"
#eval test_failure var "*_a_1bc"
#eval test var "abc$" "abc"

inductive Expr
| Add : Expr → Expr → Expr
| Num : nat → Expr
| Var : string → Expr

open Expr

instance eq_expr : decidable_eq Expr
| (Var x)     (Var y)     := if h : x = y then is_true (h ▸ rfl)
                             else is_false (λ h', Expr.no_confusion h' (λ h', absurd h' h))
| (Var x)     (Num n)     := is_false (λ h, Expr.no_confusion h)
| (Var x)     (Add e₁ e₂) := is_false (λ h, Expr.no_confusion h)
| (Num n)     (Num m)     := if h : n = m then is_true (h ▸ rfl)
                             else is_false (λ h', Expr.no_confusion h' (λ h', absurd h' h))
| (Num n)     (Var y)     := is_false (λ h, Expr.no_confusion h)
| (Num n)     (Add e₁ e₂) := is_false (λ h, Expr.no_confusion h)
| (Add e₁ e₂) (Num n)     := is_false (λ h, Expr.no_confusion h)
| (Add e₁ e₂) (Var y)     := is_false (λ h, Expr.no_confusion h)
| (Add e₁ e₂) (Add e₃ e₄) :=
  match eq_expr e₁ e₃ with
  | is_true h   := match eq_expr e₂ e₄ with
                   | is_true  h' := is_true (h ▸ h' ▸ rfl)
                   | is_false h' := is_false (λ he, Expr.no_confusion he (λ h₁ h₂, absurd h₂ h'))
                   end
  | is_false h := is_false (λ he, Expr.no_confusion he (λ h₁ h₂, absurd h₁ h))
  end

def parse_atom (p : parser Expr) : parser Expr :=
(Var <$> lexeme var <?> "variable")
<|>
(Num <$> lexeme num <?> "numeral")
<|>
(paren p)

def parse_add (p : parser Expr) : parser Expr :=
do l ← parse_atom p,
   (do symbol '+', r ← p, return $ Add l r) <|> return l

def parse_expr : parser Expr :=
whitespace >> fix (λ F, parse_add F) <* eoi

#eval test parse_expr "10" (Num 10)
#eval test parse_expr "(20)" (Num 20)
#eval test parse_expr "a" (Var "a")
#eval test parse_expr "(20 + a)" (Add (Num 20) (Var "a"))
#eval test parse_expr "  (20 + (a) + 2 ) " (Add (Num 20) (Add (Var "a") (Num 2)))

/- Failures -/
#print "Failure 1"
#eval test parse_expr "(20 +" (Num 0)
#print "---------"
#print "Failure 2"
#eval test parse_expr ""      (Num 0)
#print "---------"

namespace paper_ex
#print "Failure 3"
def digit  : parser char := lean.parser.digit <?> "digit"
def letter : parser char := lean.parser.alpha <?> "letter"
def tst    : parser char := (digit <|> return '0') >> letter
#eval test tst "*" 'a'
#print "---------"
end paper_ex
