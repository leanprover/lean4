-- Copyright (c) 2016 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
prelude
import init.string init.bool init.subtype init.unsigned init.prod init.sum
open bool list sum prod sigma subtype nat

universe variables u v

class has_to_string (A : Type u) :=
(to_string : A → string)

definition to_string {A : Type u} [has_to_string A] : A → string :=
has_to_string.to_string

instance : has_to_string bool :=
⟨λ b, cond b "tt" "ff"⟩

instance {p : Prop} : has_to_string (decidable p) :=
-- Remark: type class inference will not consider local instance `b` in the new elaborator
⟨λ b : decidable p, @ite p b _ "tt" "ff"⟩

definition list.to_string_aux {A : Type u} [has_to_string A] : bool → list A → string
| b  []      := ""
| tt (x::xs) := to_string x ++ list.to_string_aux ff xs
| ff (x::xs) := ", " ++ to_string x ++ list.to_string_aux ff xs

definition list.to_string {A : Type u} [has_to_string A] : list A → string
| []      := "[]"
| (x::xs) := "[" ++ list.to_string_aux tt (x::xs) ++ "]"

instance {A : Type u} [has_to_string A] : has_to_string (list A) :=
⟨list.to_string⟩

instance : has_to_string unit :=
⟨λ u, "star"⟩

instance {A : Type u} [has_to_string A] : has_to_string (option A) :=
⟨λ o, match o with | none := "none" | (some a) := "(some " ++ to_string a ++ ")" end⟩

instance {A : Type u} {B : Type v} [has_to_string A] [has_to_string B] : has_to_string (A ⊕ B) :=
⟨λ s, match s with | (inl a) := "(inl " ++ to_string a ++ ")" | (inr b) := "(inr " ++ to_string b ++ ")" end⟩

instance {A : Type u} {B : Type v} [has_to_string A] [has_to_string B] : has_to_string (A × B) :=
⟨λ p, "(" ++ to_string (fst p) ++ ", " ++ to_string (snd p) ++ ")"⟩

instance {A : Type u} {B : A → Type v} [has_to_string A] [s : ∀ x, has_to_string (B x)] : has_to_string (sigma B) :=
⟨λ p, "⟨"  ++ to_string (fst p) ++ ", " ++ to_string (snd p) ++ "⟩"⟩

instance {A : Type u} {P : A → Prop} [has_to_string A] : has_to_string (subtype P) :=
⟨λ s, to_string (elt_of s)⟩

definition char.quote_core (c : char) : string :=
if       c = '\n' then "\\n"
else if  c = '\\' then "\\\\"
else if  c = '\"' then "\\\""
else if  c = '\'' then "\\\'"
else c::nil

instance : has_to_string char :=
⟨λ c, "'" ++ char.quote_core c ++ "'"⟩

definition string.quote_aux : string → string
| []      := ""
| (x::xs) := string.quote_aux xs ++ char.quote_core x

definition string.quote : string → string
| []      := "\"\""
| (x::xs) := "\"" ++ string.quote_aux (x::xs) ++ "\""

instance : has_to_string string :=
⟨string.quote⟩

/- Remark: the code generator replaces this definition with one that display natural numbers in decimal notation -/
definition nat.to_string : nat → string
| 0        := "zero"
| (succ a) := "(succ " ++ nat.to_string a ++ ")"

instance : has_to_string nat :=
⟨nat.to_string⟩

instance (n : nat) : has_to_string (fin n) :=
⟨λ f, to_string (fin.val f)⟩

instance : has_to_string unsigned :=
⟨λ n, to_string (fin.val n)⟩
