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

class has_repr (α : Type u) :=
(repr : α → string)

def repr {α : Type u} [has_repr α] : α → string :=
has_repr.repr

instance : has_repr bool :=
⟨λ b, cond b "tt" "ff"⟩

instance {p : Prop} : has_repr (decidable p) :=
-- Remark: type class inference will not consider local instance `b` in the new elaborator
⟨λ b : decidable p, @ite p b _ "tt" "ff"⟩

protected def list.repr_aux {α : Type u} [has_repr α] : bool → list α → string
| b  []      := ""
| tt (x::xs) := repr x ++ list.repr_aux ff xs
| ff (x::xs) := ", " ++ repr x ++ list.repr_aux ff xs

protected def list.repr {α : Type u} [has_repr α] : list α → string
| []      := "[]"
| (x::xs) := "[" ++ list.repr_aux tt (x::xs) ++ "]"

instance {α : Type u} [has_repr α] : has_repr (list α) :=
⟨list.repr⟩

instance : has_repr unit :=
⟨λ u, "star"⟩

instance {α : Type u} [has_repr α] : has_repr (option α) :=
⟨λ o, match o with | none := "none" | (some a) := "(some " ++ repr a ++ ")" end⟩

instance {α : Type u} {β : Type v} [has_repr α] [has_repr β] : has_repr (α ⊕ β) :=
⟨λ s, match s with | (inl a) := "(inl " ++ repr a ++ ")" | (inr b) := "(inr " ++ repr b ++ ")" end⟩

instance {α : Type u} {β : Type v} [has_repr α] [has_repr β] : has_repr (α × β) :=
⟨λ ⟨a, b⟩, "(" ++ repr a ++ ", " ++ repr b ++ ")"⟩

instance {α : Type u} {β : α → Type v} [has_repr α] [s : ∀ x, has_repr (β x)] : has_repr (sigma β) :=
⟨λ ⟨a, b⟩, "⟨"  ++ repr a ++ ", " ++ repr b ++ "⟩"⟩

instance {α : Type u} {p : α → Prop} [has_repr α] : has_repr (subtype p) :=
⟨λ s, repr (val s)⟩

namespace nat

def digit_char (n : ℕ) : char :=
if n = 0 then '0' else
if n = 1 then '1' else
if n = 2 then '2' else
if n = 3 then '3' else
if n = 4 then '4' else
if n = 5 then '5' else
if n = 6 then '6' else
if n = 7 then '7' else
if n = 8 then '8' else
if n = 9 then '9' else
if n = 0xa then 'a' else
if n = 0xb then 'b' else
if n = 0xc then 'c' else
if n = 0xd then 'd' else
if n = 0xe then 'e' else
if n = 0xf then 'f' else
'*'

def digit_succ (base : ℕ) : list ℕ → list ℕ
| [] := [1]
| (d::ds) :=
    if d+1 = base then
        0 :: digit_succ ds
    else
        (d+1) :: ds

def to_digits (base : ℕ) : ℕ → list ℕ
| 0 := [0]
| (n+1) := digit_succ base (to_digits n)

protected def repr (n : ℕ) : string :=
((to_digits 10 n).map digit_char).reverse.as_string

end nat

instance : has_repr nat :=
⟨nat.repr⟩

def hex_digit_repr (n : nat) : string :=
string.singleton $ nat.digit_char n

def char_to_hex (c : char) : string :=
let n  := char.to_nat c,
    d2 := n / 16,
    d1 := n % 16
in hex_digit_repr d2 ++ hex_digit_repr d1

def char.quote_core (c : char) : string :=
if       c = '\n' then "\\n"
else if  c = '\t' then "\\t"
else if  c = '\\' then "\\\\"
else if  c = '\"' then "\\\""
else if  c.to_nat <= 31 ∨ c = '\x7f' then "\\x" ++ char_to_hex c
else string.singleton c

instance : has_repr char :=
⟨λ c, "'" ++ char.quote_core c ++ "'"⟩

def string.quote_aux : list char → string
| []      := ""
| (x::xs) := char.quote_core x ++ string.quote_aux xs

def string.quote (s : string) : string :=
if s.is_empty = tt then "\"\""
else "\"" ++ string.quote_aux s.to_list ++ "\""

instance : has_repr string :=
⟨string.quote⟩

instance (n : nat) : has_repr (fin n) :=
⟨λ f, repr (fin.val f)⟩

instance : has_repr unsigned :=
⟨λ n, repr (fin.val n)⟩

def char.repr (c : char) : string :=
repr c
