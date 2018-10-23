import init.lean.parser.identifier init.lean.ir.parser init.lean.ir.format
open lean.parser
open lean.parser.monad_parsec

def test {α} [decidable_eq α] (p : parsec' α) (s : string) (e : α) : eio unit :=
match parsec.parse p s with
| except.ok a    := if a = e then pure () else io.println "unexpected result"
| except.error e := io.println e

def test_failure {α} (p : parsec' α) (s : string) : eio unit :=
match parsec.parse p s with
| except.ok a    := io.println "unexpected success"
| except.error e := pure ()

def show_result {α} [has_to_string α] (p : parsec' α) (s : string) : eio unit :=
match parsec.parse p s with
| except.ok a    := io.println "result: " *> io.println (repr $ to_string a)
| except.error e := io.println e

#eval test (ch 'a') "a" 'a'
#eval test any "a" 'a'
#eval test any "b" 'b'
#eval test (str "foo" <|> str "bla" <|> str "boo") "bla" "bla"
#eval test ((str "foo" *> str "foo") <|> str "bla" <|> str "boo") "bla" "bla"
#eval test_failure ((str "foo" *> str "foo") <|> str "foo2" <|> str "boo") "foo2"
#eval test (try (str "foo" *> str "foo") <|> str "foo2" <|> str "boo") "foo2" "foo2"
#eval test num "1000" 1000
#eval test (do n ← num, whitespace, m ← num, pure (n, m)) "1000 200" (1000, 200)
#eval test (do n ← num, whitespace, m ← num, pure (n, m)) "1000      200" (1000, 200)
#eval test (do n ← lexeme num, m ← num, pure (n, m)) "1000 200" (1000, 200)
#eval test (whitespace *> prod.mk <$> (lexeme num) <*> (lexeme num)) "    1000 200    " (1000, 200)
#eval test (whitespace *> prod.mk <$> (lexeme num) <*> (lexeme num) <* eoi) "    1000 200    " (1000, 200)
#eval test_failure (whitespace *> prod.mk <$> (lexeme num) <*> num <* eoi) "    1000 200    "

#eval test_failure ((ch 'a' *> ch 'b') <|> (ch 'a' *> ch 'c')) "ac"
#eval test ((lookahead (str "ab") *> ch 'a' *> ch 'b') <|> (ch 'a' *> ch 'c')) "ac" 'c'
#eval test (str "ab" *> pure () <|> (ch 'a' *> ch 'c' *> pure ())) "ac" ()
#eval test (try (ch 'a' *> ch 'b') <|> (ch 'a' *> ch 'c')) "ac" 'c'
#eval test (lookahead (ch 'a')) "abc" 'a'
#eval test_failure (not_followed_by (lookahead (ch 'a'))) "abc"

def symbol (c : char) : parsec' char :=
lexeme (ch c) <?> repr c

def paren {α} (p : parsec' α) : parsec' α :=
symbol '(' *> lexeme p <* symbol ')'

#eval test (paren num) "(   10 )" 10
#eval test (paren num) "(12)" 12
#eval test (paren num) "(0)" 0
#eval test (paren num) "(0    )" 0

def var : parsec' string :=
do c ← satisfy (λ a, a.is_alpha || a = '_'),
   r ← lexeme $ take_while (λ a, a.is_digit || a.is_alpha || a = '_'),
   pure (c.to_string ++ r)

#eval test var "abc" "abc"
#eval test var "_a_1bc" "_a_1bc"
#eval test (paren var) "(_a_1bc )" "_a_1bc"
#eval test_failure var "1_a_1bc"
#eval test_failure var "*_a_1bc"
#eval test var "abc$" "abc"

open lean

#eval test identifier "«!!aaa».b1'" (mk_str_name (mk_simple_name "!!aaa") "b1'")
#eval test identifier "a" (mk_simple_name "a")
#eval test identifier "a'" (mk_simple_name "a'")
#eval test identifier "_" (mk_simple_name "_")
#eval test identifier "_a1" (mk_simple_name "_a1")
#eval test identifier "aaa.bbb._αc" (mk_str_name (mk_str_name (mk_simple_name "aaa") "bbb") "_αc")
#eval test identifier "«!a!aa».b12.ccc" (mk_str_name (mk_str_name (mk_simple_name "!a!aa") "b12") "ccc")
#eval test_failure identifier "1_a_1bc"
#eval test_failure identifier "!"
#eval test_failure identifier "1"
#eval test_failure identifier "'a"
#eval test_failure identifier ""
#eval test_failure identifier " "

#eval test parse_string_literal "\"abc\"" "abc"
#eval test parse_string_literal "\"\\\\abc\"" "\\abc"
#eval test parse_string_literal "\"\"" ""
#eval test parse_string_literal "\"\\\"\"" "\""
#eval test parse_string_literal "\"\\\'\"" "\'"
#eval test parse_string_literal "\"\\n\"" "\n"
#eval test parse_string_literal "\"\\t\"" "\t"
#eval test parse_string_literal "\"\\x4e\"" "N"
#eval test parse_string_literal "\"\\x4E\"" "N"
#eval test parse_string_literal "\"\\x7D\"" "}"
#eval test parse_string_literal "\"\\u03b1\\u03b1\"" "αα"
#eval test_failure parse_string_literal "\"abc"
#eval test_failure parse_string_literal "\"\\abc\""
#eval test_failure parse_string_literal "\"\\x4z\""
#eval test_failure parse_string_literal "\"\\x4\""
#eval test_failure parse_string_literal "\"\\u03b\\u03b1\""
#eval test_failure parse_string_literal "\"\\u03bz\\u03b1\""

def parse_instr_pp : parsec' string :=
do cmd ← lean.ir.parse_instr,
   pure $ to_string cmd

#eval test parse_instr_pp "x :    uint32 :=  10" "x : uint32 := 10"
#eval test parse_instr_pp "x : bool:=not y" "x : bool := not y"
#eval test parse_instr_pp "x : bool := and z   y" "x : bool := and z y"
#eval test parse_instr_pp "x := call f z w" "x := call f z w"
#eval test parse_instr_pp "x := call f z   w" "x := call f z w"
#eval test parse_instr_pp "o := cnstr 0   3   0" "o := cnstr 0 3 0"
#eval test parse_instr_pp "set o 0 x" "set o 0 x"
#eval test parse_instr_pp "x := get o 0" "x := get o 0"
#eval test parse_instr_pp "sset o 8 x" "sset o 8 x"
#eval test parse_instr_pp "x : bool := sget o 24" "x : bool := sget o 24"
#eval test parse_instr_pp "x := closure f a" "x := closure f a"
#eval test parse_instr_pp "x := closure f a b" "x := closure f a b"
#eval test parse_instr_pp "x := apply f a" "x := apply f a"
#eval test parse_instr_pp "x := array sz c" "x := array sz c"
#eval test parse_instr_pp "array_write a i v" "array_write a i v"
#eval test parse_instr_pp "x : object := array_read a i" "x : object := array_read a i"
#eval test parse_instr_pp "x := sarray uint32 sz c" "x := sarray uint32 sz c"
#eval test parse_instr_pp "array_write a i v" "array_write a i v"
#eval test parse_instr_pp "x : uint64 := array_read a i" "x : uint64 := array_read a i"
#eval test parse_instr_pp "inc x" "inc x"
#eval test parse_instr_pp "dec x" "dec x"
#eval test parse_instr_pp "dec_sref x" "dec_sref x"
#eval test parse_instr_pp "free x" "free x"
#eval test parse_instr_pp "x := call  f" "x := call f"
#eval test parse_instr_pp "x:uint32:=   array_read y   z" "x : uint32 := array_read y z"

inductive Expr
| Add : Expr → Expr → Expr
| Num : nat → Expr
| Var : string → Expr

open Expr

def eq_expr : Π a b : Expr, decidable (a = b)
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
  | is_true h   := (match eq_expr e₂ e₄ with
                    | is_true  h' := is_true (h ▸ h' ▸ rfl)
                    | is_false h' := is_false (λ he, Expr.no_confusion he (λ h₁ h₂, absurd h₂ h')))
  | is_false h := is_false (λ he, Expr.no_confusion he (λ h₁ h₂, absurd h₁ h))

instance : decidable_eq Expr :=
{dec_eq := eq_expr}

def parse_atom (p : parsec' Expr) : parsec' Expr :=
(Var <$> lexeme var <?> "variable")
<|>
(Num <$> lexeme num <?> "numeral")
<|>
(paren p)

def parse_add (p : parsec' Expr) : parsec' Expr :=
do l ← parse_atom p,
   (do symbol '+', r ← p, pure $ Add l r) <|> pure l

def parse_expr : parsec' Expr :=
whitespace *> fix (λ F, parse_add F) <* eoi

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
def digit  : parsec' char := monad_parsec.digit <?> "digit"
def letter : parsec' char := monad_parsec.alpha <?> "letter"
def tst    : parsec' char := (digit <|> pure '0') *> letter
#eval test tst "*" 'a'
#print "---------"
end paper_ex
