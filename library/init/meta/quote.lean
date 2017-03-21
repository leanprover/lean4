/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import init.meta.tactic

open tactic

meta class has_quote (α : Type) :=
(quote : α → pexpr)

@[inline] meta def quote {α : Type} [has_quote α] : α → pexpr :=
has_quote.quote

meta instance : has_quote bool :=
⟨λ b, if b then ``(true) else ``(false)⟩

meta instance : has_quote nat := ⟨pexpr.mk_prenum_macro⟩
@[priority std.priority.default + 1]
meta instance : has_quote string := ⟨pexpr.mk_string_macro⟩
meta instance : has_quote pexpr := ⟨pexpr.mk_quote_macro⟩

meta instance : has_quote char :=
⟨λ ⟨n, pr⟩, ``(char.of_nat %%(quote n))⟩

meta instance : has_quote unsigned :=
⟨λ ⟨n, pr⟩, ``(unsigned.of_nat' %%(quote n))⟩

meta instance : has_quote pos :=
⟨λ ⟨l, c⟩, ``(pos.mk %%(quote l) %%(quote c))⟩

meta def name.quote : name → pexpr
| name.anonymous        := ``(name.anonymous)
| (name.mk_string s n)  := ``(name.mk_string  %%(quote s) %%(name.quote n))
| (name.mk_numeral i n) := ``(name.mk_numeral %%(quote i) %%(name.quote n))

meta instance : has_quote name := ⟨name.quote⟩

private meta def list.quote {α : Type} [has_quote α] : list α → pexpr
| []     := ``([])
| (h::t) := ``(%%(quote h) :: %%(list.quote t))

meta instance {α : Type} [has_quote α] : has_quote (list α) := ⟨list.quote⟩

meta instance {α : Type} [has_quote α] : has_quote (option α) :=
⟨λ opt, match opt with
| some x := ``(option.some %%(quote x))
| none   := ``(option.none)
end⟩

meta instance : has_quote unit := ⟨λ _, ``(unit.star)⟩

meta instance {α β : Type} [has_quote α] [has_quote β] : has_quote (α × β) :=
⟨λ ⟨x, y⟩, ``((%%(quote x), %%(quote y)))⟩
