/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.options

universe variables u v

inductive format.color
| red | green | orange | blue | pink | cyan | grey

meta constant format : Type 1
meta constant format.line            : format
meta constant format.space           : format
meta constant format.nil             : format
meta constant format.compose         : format → format → format
meta constant format.nest            : nat → format → format
meta constant format.highlight       : format → color → format
meta constant format.group           : format → format
meta constant format.of_string       : string → format
meta constant format.of_nat          : nat → format
meta constant format.flatten         : format → format
meta constant format.to_string       : format → options → string
meta constant format.of_options      : options → format
meta constant format.is_nil          : format → bool
meta constant trace_fmt {A : Type u} : format → (unit → A) → A


attribute [instance]
meta definition format.is_inhabited : inhabited format :=
inhabited.mk format.space

attribute [instance]
meta definition format_has_append : has_append format :=
has_append.mk format.compose

attribute [instance]
meta definition format_has_to_string : has_to_string format :=
has_to_string.mk (λ f, format.to_string f options.mk)

structure [class] has_to_format (A : Type u) :=
(to_format : A → format)

attribute [instance]
meta definition format_has_to_format : has_to_format format :=
has_to_format.mk id

meta definition to_fmt {A : Type u} [has_to_format A] : A → format :=
has_to_format.to_format

attribute [instance]
meta definition coe_nat_to_format : has_coe nat format :=
has_coe.mk format.of_nat

attribute [instance]
meta definition coe_string_to_format : has_coe string format :=
has_coe.mk format.of_string

open format list

meta definition format.when {A : Type u} [has_to_format A] : bool → A → format
| tt a := to_fmt a
| ff a := nil

attribute [instance]
meta definition options.has_to_format : has_to_format options :=
has_to_format.mk (λ o, format.of_options o)

attribute [instance]
meta definition bool.has_to_format : has_to_format bool :=
has_to_format.mk (λ b, if b then of_string "tt" else of_string "ff")

attribute [instance]
meta definition decidable.has_to_format {p : Prop} : has_to_format (decidable p) :=
has_to_format.mk (λ b : decidable p, @ite p b _ (of_string "tt") (of_string "ff"))

attribute [instance]
meta definition string.has_to_format : has_to_format string :=
has_to_format.mk (λ s, format.of_string s)

attribute [instance]
meta definition nat.has_to_format : has_to_format nat :=
has_to_format.mk (λ n, format.of_nat n)

attribute [instance]
meta definition char.has_to_format : has_to_format char :=
has_to_format.mk (λ c : char, format.of_string [c])

meta definition list.to_format_aux {A : Type u} [has_to_format A] : bool → list A → format
| b  []      := to_fmt ""
| tt (x::xs) := to_fmt x ++ list.to_format_aux ff xs
| ff (x::xs) := to_fmt "," ++ line ++ to_fmt x ++ list.to_format_aux ff xs

meta definition list.to_format {A : Type u} [has_to_format A] : list A → format
| []      := to_fmt "[]"
| (x::xs) := to_fmt "[" ++ group (nest 1 (list.to_format_aux tt (x::xs))) ++ to_fmt "]"

attribute [instance]
meta definition list.has_to_format {A : Type u} [has_to_format A] : has_to_format (list A) :=
has_to_format.mk list.to_format

attribute [instance] string.has_to_format

attribute [instance]
meta definition name.has_to_format : has_to_format name :=
has_to_format.mk (λ n, to_fmt (to_string n))

attribute [instance]
meta definition unit.has_to_format : has_to_format unit :=
has_to_format.mk (λ u, to_fmt "()")

attribute [instance]
meta definition option.has_to_format {A : Type u} [has_to_format A] : has_to_format (option A) :=
has_to_format.mk (λ o, option.cases_on o
  (to_fmt "none")
  (λ a, to_fmt "(some " ++ nest 6 (to_fmt a) ++ to_fmt ")"))

attribute [instance]
meta definition sum.has_to_format {A : Type u} {B : Type v} [has_to_format A] [has_to_format B] : has_to_format (sum A B) :=
has_to_format.mk (λ s, sum.cases_on s
  (λ a, to_fmt "(inl " ++ nest 5 (to_fmt a) ++ to_fmt ")")
  (λ b, to_fmt "(inr " ++ nest 5 (to_fmt b) ++ to_fmt ")"))

open prod

attribute [instance]
meta definition prod.has_to_format {A : Type u} {B : Type v} [has_to_format A] [has_to_format B] : has_to_format (prod A B) :=
has_to_format.mk (λ p, group (nest 1 (to_fmt "(" ++ to_fmt (fst p) ++ to_fmt "," ++ line ++ to_fmt (snd p) ++ to_fmt ")")))

open sigma

attribute [instance]
meta definition sigma.has_to_format {A : Type u} {B : A → Type v} [has_to_format A] [s : ∀ x, has_to_format (B x)]
                                          : has_to_format (sigma B) :=
has_to_format.mk (λ p, group (nest 1 (to_fmt "⟨"  ++ to_fmt (fst p) ++ to_fmt "," ++ line ++ to_fmt (snd p) ++ to_fmt "⟩")))

open subtype

attribute [instance]
meta definition subtype.has_to_format {A : Type u} {P : A → Prop} [has_to_format A] : has_to_format (subtype P) :=
has_to_format.mk (λ s, to_fmt (elt_of s))

meta definition format.bracket : string → string → format → format
| o c f := to_fmt o ++ nest (utf8_length o) f ++ to_fmt c

meta definition format.paren (f : format) : format :=
format.bracket "(" ")" f

meta definition format.cbrace (f : format) : format :=
format.bracket "{" "}" f

meta definition format.sbracket (f : format) : format :=
format.bracket "[" "]" f

meta definition format.dcbrace (f : format) : format :=
to_fmt "⦃" ++ nest 1 f ++ to_fmt "⦄"
