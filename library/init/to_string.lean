-- Copyright (c) 2016 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
prelude
import init.string init.bool init.subtype init.unsigned
open bool list sum prod sigma subtype nat

structure has_to_string [class] (A : Type) :=
(to_string : A → string)

definition to_string {A : Type} [has_to_string A] : A → string :=
has_to_string.to_string

definition bool.has_to_string [instance] : has_to_string bool :=
has_to_string.mk (λ b, cond b "tt" "ff")

definition decidable.has_to_string [instance] {p : Prop} : has_to_string (decidable p) :=
has_to_string.mk (λ b, if p then "tt" else "ff")

definition list.to_string_aux {A : Type} [has_to_string A] : bool → list A → string
| _  []      := ""
| tt (x::xs) := to_string x + list.to_string_aux ff xs
| ff (x::xs) := ", " + to_string x + list.to_string_aux ff xs

definition list.to_string {A : Type} [has_to_string A] : list A → string
| []      := "[]"
| (x::xs) := "[" + list.to_string_aux tt (x::xs) + "]"

definition list.has_to_string [instance] {A : Type} [has_to_string A] : has_to_string (list A) :=
has_to_string.mk list.to_string

definition unit.has_to_string [instance] : has_to_string unit :=
has_to_string.mk (λ u, "star")

definition option.has_to_string [instance] {A : Type} [has_to_string A] : has_to_string (option A) :=
has_to_string.mk (λ o, match o with | none := "none" | some a := "(some " + to_string a + ")" end)

definition sum.has_to_string [instance] {A B : Type} [has_to_string A] [has_to_string B] : has_to_string (sum A B) :=
has_to_string.mk (λ s, match s with | inl a := "(inl " + to_string a + ")" | inr b := "(inr " + to_string b + ")" end)

definition prod.has_to_string [instance] {A B : Type} [has_to_string A] [has_to_string B] : has_to_string (prod A B) :=
has_to_string.mk (λ p, "(" + to_string (pr1 p) + ", " + to_string (pr2 p) + ")")

definition sigma.has_to_string [instance] {A : Type} {B : A → Type} [has_to_string A] [s : ∀ x, has_to_string (B x)]
                                          : has_to_string (sigma B) :=
has_to_string.mk (λ p, "⟨"  + to_string (pr1 p) + ", " + to_string (pr2 p) + "⟩")

definition subtype.has_to_string [instance] {A : Type} {P : A → Prop} [has_to_string A] : has_to_string (subtype P) :=
has_to_string.mk (λ s, to_string (elt_of s))

definition char.quote_core (c : char) : string :=
if       char.to_nat c = 10 then "\\n"
else if  char.to_nat c = 92 then "\\\\"
else if  char.to_nat c = 34 then "\\\""
else c::nil

definition char.has_to_sting [instance] : has_to_string char :=
has_to_string.mk (λ c, "'" + char.quote_core c + "'")

definition string.quote_aux : string → string
| []      := ""
| (x::xs) := string.quote_aux xs + char.quote_core x

definition string.quote : string → string
| []      := "\"\""
| (x::xs) := "\"" + string.quote_aux (x::xs) + "\""

definition string.has_to_string [instance] : has_to_string string :=
has_to_string.mk string.quote

/- Remark: the code generator replaces this definition with one that display natural numbers in decimal notation -/
definition nat.to_string : nat → string
| 0        := "zero"
| (succ a) := "(succ " + nat.to_string a + ")"

definition nat.has_to_string [instance] : has_to_string nat :=
has_to_string.mk nat.to_string

definition fin.has_to_string [instance] (n : nat) : has_to_string (fin n) :=
has_to_string.mk (λ f, to_string (fin.val f))

definition unsigned.has_to_string [instance] : has_to_string unsigned :=
has_to_string.mk (λ n, to_string (fin.val n))
