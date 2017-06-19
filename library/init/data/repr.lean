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

/- Remark: the code generator replaces this definition with one that display natural numbers in decimal notation -/
protected def nat.repr : nat → string
| 0        := "zero"
| (succ a) := "(succ " ++ nat.repr a ++ ")"

instance : has_repr nat :=
⟨nat.repr⟩

def hex_digit_repr (n : nat) : string :=
if n ≤ 9 then repr n
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
in hex_digit_repr d2 ++ hex_digit_repr d1

def char.quote_core (c : char) : string :=
if       c = '\n' then "\\n"
else if  c = '\t' then "\\t"
else if  c = '\\' then "\\\\"
else if  c = '\"' then "\\\""
else if  char.to_nat c <= 31 then "\\x" ++ char_to_hex c
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
