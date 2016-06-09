/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.options

inductive format.color :=
| red | green | orange | blue | pink | cyan | grey

meta_constant format : Type₁
meta_constant format.line          : format
meta_constant format.space         : format
meta_constant format.compose       : format → format → format
meta_constant format.nest          : nat → format → format
meta_constant format.highlight     : format → color → format
meta_constant format.group         : format → format
meta_constant format.of_string     : string → format
meta_constant format.of_nat        : nat → format
meta_constant format.flatten       : format → format
meta_constant format.to_string     : format → options → string
meta_constant format.of_options    : options → format
meta_constant trace_fmt {A : Type} : format → (unit → A) → A

meta_definition format_has_add [instance] : has_add format :=
has_add.mk format.compose

meta_definition format_has_to_string [instance] : has_to_string format :=
has_to_string.mk (λ f, format.to_string f options.mk)

structure has_to_format [class] (A : Type) :=
(to_format : A → format)

meta_definition to_fmt {A : Type} [has_to_format A] : A → format :=
has_to_format.to_format

namespace format
attribute [coercion] of_string of_nat
end format

open format bool list

meta_definition options.has_to_format [instance] : has_to_format options :=
has_to_format.mk (λ o, format.of_options o)

meta_definition bool.has_to_format [instance] : has_to_format bool :=
has_to_format.mk (λ b, cond b "tt" "ff")

meta_definition decidable.has_to_format [instance] {p : Prop} : has_to_format (decidable p) :=
has_to_format.mk (λ b, if p then "tt" else "ff")

meta_definition string.has_to_format [instance] : has_to_format string :=
has_to_format.mk (λ s, format.of_string s)

meta_definition nat.has_to_format [instance] : has_to_format nat :=
has_to_format.mk (λ n, format.of_nat n)

meta_definition char.has_to_format [instance] : has_to_format char :=
has_to_format.mk (λ c : char, format.of_string [c])

meta_definition list.to_format_aux {A : Type} [has_to_format A] : bool → list A → format
| _  []      := ""
| tt (x::xs) := to_fmt x + list.to_format_aux ff xs
| ff (x::xs) := "," + line + to_fmt x + list.to_format_aux ff xs

meta_definition list.to_format {A : Type} [has_to_format A] : list A → format
| []      := "[]"
| (x::xs) := "[" + group (nest 1 (list.to_format_aux tt (x::xs))) + "]"

meta_definition list.has_to_format [instance] {A : Type} [has_to_format A] : has_to_format (list A) :=
has_to_format.mk list.to_format

attribute [instance] string.has_to_format

meta_definition name.has_to_format [instance] : has_to_format name :=
has_to_format.mk (λ n, to_string n)

meta_definition unit.has_to_format [instance] : has_to_format unit :=
has_to_format.mk (λ u, "star")

meta_definition option.has_to_format [instance] {A : Type} [has_to_format A] : has_to_format (option A) :=
has_to_format.mk (λ o, option.cases_on o
  "none"
  (λ a, "(some " + nest 6 (to_fmt a) + ")"))

meta_definition sum.has_to_format [instance] {A B : Type} [has_to_format A] [has_to_format B] : has_to_format (sum A B) :=
has_to_format.mk (λ s, sum.cases_on s
  (λ a, "(inl " + nest 5 (to_fmt a) + ")")
  (λ b, "(inr " + nest 5 (to_fmt b) + ")"))

open prod

meta_definition prod.has_to_format [instance] {A B : Type} [has_to_format A] [has_to_format B] : has_to_format (prod A B) :=
has_to_format.mk (λ p, group (nest 1 ("(" + to_fmt (pr1 p) + "," + line + to_fmt (pr2 p) + ")")))

open sigma

meta_definition sigma.has_to_format [instance] {A : Type} {B : A → Type} [has_to_format A] [s : ∀ x, has_to_format (B x)]
                                          : has_to_format (sigma B) :=
has_to_format.mk (λ p, group (nest 1 ("⟨"  + to_fmt (pr1 p) + "," + line + to_fmt (pr2 p) + "⟩")))

open subtype

meta_definition subtype.has_to_format [instance] {A : Type} {P : A → Prop} [has_to_format A] : has_to_format (subtype P) :=
has_to_format.mk (λ s, to_fmt (elt_of s))
