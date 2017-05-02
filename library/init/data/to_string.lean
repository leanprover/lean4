/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.string.basic init.data.bool.basic init.data.subtype.basic
import init.data.unsigned.basic init.data.prod init.data.sum.basic init.data.nat.div
open sum subtype nat

universes u v

class has_to_string (α : Type u) :=
(to_string : α → string)

def to_string {α : Type u} [has_to_string α] : α → string :=
has_to_string.to_string

instance : has_to_string bool :=
⟨λ b, cond b "tt" "ff"⟩

instance {p : Prop} : has_to_string (decidable p) :=
-- Remark: type class inference will not consider local instance `b` in the new elaborator
⟨λ b : decidable p, @ite p b _ "tt" "ff"⟩

protected def list.to_string_aux {α : Type u} [has_to_string α] : bool → list α → string
| b  []      := ""
| tt (x::xs) := to_string x ++ list.to_string_aux ff xs
| ff (x::xs) := ", " ++ to_string x ++ list.to_string_aux ff xs

protected def list.to_string {α : Type u} [has_to_string α] : list α → string
| []      := "[]"
| (x::xs) := "[" ++ list.to_string_aux tt (x::xs) ++ "]"

instance {α : Type u} [has_to_string α] : has_to_string (list α) :=
⟨list.to_string⟩

instance : has_to_string unit :=
⟨λ u, "star"⟩

instance {α : Type u} [has_to_string α] : has_to_string (option α) :=
⟨λ o, match o with | none := "none" | (some a) := "(some " ++ to_string a ++ ")" end⟩

instance {α : Type u} {β : Type v} [has_to_string α] [has_to_string β] : has_to_string (α ⊕ β) :=
⟨λ s, match s with | (inl a) := "(inl " ++ to_string a ++ ")" | (inr b) := "(inr " ++ to_string b ++ ")" end⟩

instance {α : Type u} {β : Type v} [has_to_string α] [has_to_string β] : has_to_string (α × β) :=
⟨λ ⟨a, b⟩, "(" ++ to_string a ++ ", " ++ to_string b ++ ")"⟩

instance {α : Type u} {β : α → Type v} [has_to_string α] [s : ∀ x, has_to_string (β x)] : has_to_string (sigma β) :=
⟨λ ⟨a, b⟩, "⟨"  ++ to_string a ++ ", " ++ to_string b ++ "⟩"⟩

instance {α : Type u} {p : α → Prop} [has_to_string α] : has_to_string (subtype p) :=
⟨λ s, to_string (val s)⟩

/- Remark: the code generator replaces this definition with one that display natural numbers in decimal notation -/
protected def nat.to_string : nat → string
| 0        := "zero"
| (succ a) := "(succ " ++ nat.to_string a ++ ")"

instance : has_to_string nat :=
⟨nat.to_string⟩

def hex_digit_to_string (n : nat) : string :=
if n ≤ 9 then to_string n
else if n = 10 then "a"
else if n = 11 then "b"
else if n = 12 then "c"
else if n = 13 then "d"
else if n = 14 then "e"
else "f"

def char_to_hex (c : char) : string :=
let n  := char.to_nat c,
    d2 := n / 16,
    d1 := n % 16
in hex_digit_to_string d2 ++ hex_digit_to_string d1

def char.quote_core (c : char) : string :=
if       c = '\n' then "\\n"
else if  c = '\t' then "\\t"
else if  c = '\\' then "\\\\"
else if  c = '\"' then "\\\""
else if  char.to_nat c <= 31 then "\\x" ++ char_to_hex c
else [c]

instance : has_to_string char :=
⟨λ c, "#\"" ++ char.quote_core c ++ "\""⟩

def string.quote_aux : string → string
| []      := ""
| (x::xs) := string.quote_aux xs ++ char.quote_core x

def string.quote : string → string
| []      := "\"\""
| (x::xs) := "\"" ++ string.quote_aux (x::xs) ++ "\""

instance : has_to_string string :=
⟨string.quote⟩

instance (n : nat) : has_to_string (fin n) :=
⟨λ f, to_string (fin.val f)⟩

instance : has_to_string unsigned :=
⟨λ n, to_string (fin.val n)⟩
