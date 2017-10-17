/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.options init.function init.data.to_string

universes u v

inductive format.color
| red | green | orange | blue | pink | cyan | grey

meta constant format : Type
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
meta constant format.to_string  (f : format) (o : options := options.mk) : string
meta constant format.of_options      : options → format
meta constant format.is_nil          : format → bool
meta constant trace_fmt {α : Type u} : format → (unit → α) → α

meta instance : inhabited format :=
⟨format.space⟩

meta instance : has_append format :=
⟨format.compose⟩

meta instance : has_to_string format :=
⟨λ f, f.to_string options.mk⟩

meta class has_to_format (α : Type u) :=
(to_format : α → format)

meta instance : has_to_format format :=
⟨id⟩

meta def to_fmt {α : Type u} [has_to_format α] : α → format :=
has_to_format.to_format

meta instance nat_to_format : has_coe nat format :=
⟨format.of_nat⟩

meta instance string_to_format : has_coe string format :=
⟨format.of_string⟩

open format list

meta def format.indent (f : format) (n : nat) : format :=
nest n (line ++ f)

meta def format.when {α : Type u} [has_to_format α] : bool → α → format
| tt a := to_fmt a
| ff a := nil

meta def format.join (xs : list format) : format :=
foldl compose (of_string "") xs

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

meta instance : has_to_format unsigned :=
⟨λ n, to_fmt n.to_nat⟩

meta instance : has_to_format char :=
⟨λ c : char, format.of_string c.to_string⟩

meta def list.to_format {α : Type u} [has_to_format α] : list α → format
| [] := to_fmt "[]"
| xs := to_fmt "[" ++ group (nest 1 $ format.join $ list.intersperse ("," ++ line) $ xs.map to_fmt) ++ to_fmt "]"

meta instance {α : Type u} [has_to_format α] : has_to_format (list α) :=
⟨list.to_format⟩

attribute [instance] string.has_to_format

meta instance : has_to_format name :=
⟨λ n, to_fmt n.to_string⟩

meta instance : has_to_format unit :=
⟨λ u, to_fmt "()"⟩

meta instance {α : Type u} [has_to_format α] : has_to_format (option α) :=
⟨λ o, option.cases_on o
  (to_fmt "none")
  (λ a, to_fmt "(some " ++ nest 6 (to_fmt a) ++ to_fmt ")")⟩

meta instance sum_has_to_format {α : Type u} {β : Type v} [has_to_format α] [has_to_format β] : has_to_format (sum α β) :=
⟨λ s, sum.cases_on s
  (λ a, to_fmt "(inl " ++ nest 5 (to_fmt a) ++ to_fmt ")")
  (λ b, to_fmt "(inr " ++ nest 5 (to_fmt b) ++ to_fmt ")")⟩

open prod

meta instance {α : Type u} {β : Type v} [has_to_format α] [has_to_format β] : has_to_format (prod α β) :=
⟨λ ⟨a, b⟩, group (nest 1 (to_fmt "(" ++ to_fmt a ++ to_fmt "," ++ line ++ to_fmt b ++ to_fmt ")"))⟩

open sigma

meta instance {α : Type u} {β : α → Type v} [has_to_format α] [s : ∀ x, has_to_format (β x)]
                                          : has_to_format (sigma β) :=
⟨λ ⟨a, b⟩, group (nest 1 (to_fmt "⟨"  ++ to_fmt a ++ to_fmt "," ++ line ++ to_fmt b ++ to_fmt "⟩"))⟩

open subtype

meta instance {α : Type u} {p : α → Prop} [has_to_format α] : has_to_format (subtype p) :=
⟨λ s, to_fmt (val s)⟩

meta def format.bracket : string → string → format → format
| o c f := to_fmt o ++ nest o.length f ++ to_fmt c

meta def format.paren (f : format) : format :=
format.bracket "(" ")" f

meta def format.cbrace (f : format) : format :=
format.bracket "{" "}" f

meta def format.sbracket (f : format) : format :=
format.bracket "[" "]" f

meta def format.dcbrace (f : format) : format :=
to_fmt "⦃" ++ nest 1 f ++ to_fmt "⦄"
