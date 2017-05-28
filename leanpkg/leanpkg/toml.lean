/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
import data.buffer.parser

-- I'd like to contribute a new naming convention:
-- CamelCase for non-terminals.

def join (sep : string) : list string → string
| [x]     := x
| []      := ""
| (x::xs) := x ++ sep ++ join xs

namespace toml

inductive value : Type
| str : string → value
| nat : ℕ → value
| bool : bool → value
| table : list (string × value) → value

namespace value

private def escapec : char → string
| '\"' := "\\\""
| '\t' := "\\t"
| '\n' := "\\n"
| '\\' := "\\\\"
| c    := [c]

private def escape (s : string) : string :=
list.bind s escapec

private def to_string_core : ∀ (n : ℕ), value → string
| _ (value.str s) := "\"" ++ escape s ++ "\""
| _ (value.nat n) := n.to_string
| _ (value.bool tt) := "true"
| _ (value.bool ff) := "false"
| (n+1) (value.table cs) :=
  "{ " ++ join ", " (do (k, v) ← cs, [k ++ " = " ++ to_string_core n v]) ++ " }"
| 0 _ := "<max recursion depth reached>"

protected def to_string : ∀ (v : value), string
| (table cs) := join "\n" $ do (h, c) ← cs,
  match c with
  | table ds :=
    ["[" ++ h ++ "]\n" ++
     join "" (do (k, v) ← ds,
       [k ++ " = " ++ to_string_core 1024 v ++ "\n"])]
  | _ := ["<error> " ++ to_string_core 1024 c]
  end
| v := to_string_core (sizeof v) v

instance : has_to_string value :=
⟨value.to_string⟩

def lookup : value → string → option value
| (value.table cs) k :=
  match cs.filter (λ c : string × value, c.fst = k) with
  | [] := none
  | (k,v) ::_ := some v
  end
| _ _ := none

end value

open parser

def Comment : parser unit :=
ch '#' >> many' (sat (≠ '#')) >> optional (ch '\n') >> eps

def Ws : parser unit :=
decorate_error "<whitespace>" $
many' $ one_of' " \t\n" <|> Comment

def tok (s : string) := str s >> Ws

def StringChar : parser char :=
sat (λc, c ≠ '\"' ∧ c ≠ '\\' ∧ c.val > 0x1f)
 <|> (do str "\\",
         (str "t" >> return '\t') <|>
         (str "n" >> return '\n') <|>
         (str "\\" >> return '\\') <|>
         (str "\"" >> return '\"'))

def BasicString : parser string :=
str "\"" *> (list.reverse <$> many StringChar) <* str "\"" <* Ws

def String := BasicString

def Nat : parser nat :=
do l ← many1 (one_of "0123456789"),
   Ws,
   let s : string := l.reverse,
   return s.to_nat

def Boolean : parser bool :=
(tok "true" >> return tt) <|>
(tok "false" >> return ff)

def BareKey : parser string := do
cs ← many1 $ sat $ λ c, c.is_alpha ∨ c.is_digit ∨ c = '_' ∨ c = '-',
Ws,
return cs.reverse

def Key := BareKey <|> BasicString

section
parameter Val : parser value

def KeyVal : parser (string × value) := do
k ← Key, tok "=", v ← Val,
return (k, v)

def StdTable : parser (string × value) := do
tok "[", n ← Key, tok "]",
cs ← many KeyVal,
return (n, value.table cs)

def Table : parser (string × value) := StdTable

def StrVal : parser value :=
value.str <$> String

def NatVal : parser value :=
value.nat <$> Nat

def BoolVal : parser value :=
value.bool <$> Boolean

def InlineTable : parser value :=
tok "{" *> (value.table <$> sep_by (tok ",") KeyVal) <* tok "}"

end

def Val : parser value :=
fix $ λ Val, StrVal <|> NatVal <|> BoolVal <|> InlineTable Val

def Expression := Table Val

def File : parser value :=
Ws *> (value.table <$> many Expression)

/-
#eval run_string File $
   "[package]\n" ++
   "name = \"sss\"\n" ++
   "version = \"0.1\"\n" ++
   "timeout = 10\n" ++
   "\n" ++
   "[dependencies]\n" ++
   "library_dev = { git = \"https://github.com/leanprover/library_dev\", rev = \"master\" }"
-/

end toml
