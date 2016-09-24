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

meta instance : inhabited format :=
⟨format.space⟩

meta instance : has_append format :=
⟨format.compose⟩

meta instance : has_to_string format :=
⟨λ f, format.to_string f options.mk⟩

structure [class] has_to_format (A : Type u) :=
(to_format : A → format)

meta instance : has_to_format format :=
⟨id⟩

meta definition to_fmt {A : Type u} [has_to_format A] : A → format :=
has_to_format.to_format

meta instance nat_to_format : has_coe nat format :=
⟨format.of_nat⟩

meta instance string_to_format : has_coe string format :=
⟨format.of_string⟩

open format list

meta definition format.when {A : Type u} [has_to_format A] : bool → A → format
| tt a := to_fmt a
| ff a := nil

meta instance : has_to_format options :=
⟨λ o, format.of_options o⟩

meta instance : has_to_format bool :=
⟨λ b, if b then of_string "tt" else of_string "ff"⟩

meta instance {p : Prop} : has_to_format (decidable p) :=
⟨λ b : decidable p, @ite p b _ (of_string "tt") (of_string "ff")⟩

meta instance : has_to_format string :=
⟨λ s, format.of_string s⟩

meta instance : has_to_format nat :=
⟨λ n, format.of_nat n⟩

meta instance : has_to_format char :=
⟨λ c : char, format.of_string [c]⟩

meta definition list.to_format_aux {A : Type u} [has_to_format A] : bool → list A → format
| b  []      := to_fmt ""
| tt (x::xs) := to_fmt x ++ list.to_format_aux ff xs
| ff (x::xs) := to_fmt "," ++ line ++ to_fmt x ++ list.to_format_aux ff xs

meta definition list.to_format {A : Type u} [has_to_format A] : list A → format
| []      := to_fmt "[]"
| (x::xs) := to_fmt "[" ++ group (nest 1 (list.to_format_aux tt (x::xs))) ++ to_fmt "]"

meta instance {A : Type u} [has_to_format A] : has_to_format (list A) :=
⟨list.to_format⟩

attribute [instance] string.has_to_format

meta instance : has_to_format name :=
⟨λ n, to_fmt (to_string n)⟩

meta instance : has_to_format unit :=
⟨λ u, to_fmt "()"⟩

meta instance {A : Type u} [has_to_format A] : has_to_format (option A) :=
⟨λ o, option.cases_on o
  (to_fmt "none")
  (λ a, to_fmt "(some " ++ nest 6 (to_fmt a) ++ to_fmt ")")⟩

meta instance {A : Type u} {B : Type v} [has_to_format A] [has_to_format B] : has_to_format (sum A B) :=
⟨λ s, sum.cases_on s
  (λ a, to_fmt "(inl " ++ nest 5 (to_fmt a) ++ to_fmt ")")
  (λ b, to_fmt "(inr " ++ nest 5 (to_fmt b) ++ to_fmt ")")⟩

open prod

meta instance {A : Type u} {B : Type v} [has_to_format A] [has_to_format B] : has_to_format (prod A B) :=
⟨λ p, group (nest 1 (to_fmt "(" ++ to_fmt (fst p) ++ to_fmt "," ++ line ++ to_fmt (snd p) ++ to_fmt ")"))⟩

open sigma

meta instance {A : Type u} {B : A → Type v} [has_to_format A] [s : ∀ x, has_to_format (B x)]
                                          : has_to_format (sigma B) :=
⟨λ p, group (nest 1 (to_fmt "⟨"  ++ to_fmt (fst p) ++ to_fmt "," ++ line ++ to_fmt (snd p) ++ to_fmt "⟩"))⟩

open subtype

meta instance {A : Type u} {P : A → Prop} [has_to_format A] : has_to_format (subtype P) :=
⟨λ s, to_fmt (elt_of s)⟩

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
