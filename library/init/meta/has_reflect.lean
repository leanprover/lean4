/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import init.meta.expr init.util

@[reducible] meta def {u} has_reflect (α : Type u) := Π a : α, reflected a

meta instance bool.reflect : has_reflect bool
| tt := `(tt)
| ff := `(ff)

meta instance nat.reflect : has_reflect nat
| n := if n = 0 then unchecked_cast `(0 : nat)
       else if n % 2 = 0 then unchecked_cast $ `(λ n : nat, bit0 n).subst (nat.reflect (n / 2))
       else unchecked_cast $ `(λ n : nat, bit1 n).subst (nat.reflect (n / 2))

meta instance unsigned.reflect : has_reflect unsigned
| ⟨n, pr⟩ := unchecked_cast `(unsigned.of_nat' n)

meta instance name.reflect : has_reflect name
| name.anonymous        := `(name.anonymous)
| (name.mk_string  s n) := `(λ n, name.mk_string  s n).subst (name.reflect n)
| (name.mk_numeral i n) := `(λ n, name.mk_numeral i n).subst (name.reflect n)

meta instance list.reflect {α : Type} [has_reflect α] [reflected α] : has_reflect (list α)
| []     := `([])
| (h::t) := `(λ t, h :: t).subst (list.reflect t)

meta instance option.reflect {α : Type} [has_reflect α] [reflected α] : has_reflect (option α)
| (some x) := `(_)
| none     := `(_)

meta instance unit.reflect : has_reflect unit
| () := `(_)

meta instance prod.reflect {α β : Type} [has_reflect α] [reflected α] [has_reflect β] [reflected β]
  : has_reflect (α × β)
| ⟨x, y⟩ := `(_)

meta instance pos.reflect : has_reflect pos
| ⟨l, c⟩ := `(_)
