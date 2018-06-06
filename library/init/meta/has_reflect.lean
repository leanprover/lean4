/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import init.meta.expr init.util init.meta.pexpr

@[reducible] meta def {u} has_reflect (α : Sort u) := Π a : α, reflected a

section
local attribute [semireducible] reflected uint32 uint64

meta instance nat.reflect : has_reflect ℕ
| n := if n = 0 then `(0 : ℕ)
       else if n = 1 then `(1 : ℕ)
       else if n % 2 = 0 then `(bit0 %%(nat.reflect (n / 2)) : ℕ)
       else `(bit1 %%(nat.reflect (n / 2)) : ℕ)

meta instance uint32.reflect : has_reflect uint32
| ⟨n, pr⟩ := `(uint32.of_nat n)

meta instance uint64.reflect : has_reflect uint64
| ⟨n, pr⟩ := `(uint64.of_nat n)
end

/- Instances that [derive] depends on. All other basic instances are defined at the end of
   derive.lean. -/

meta instance name.reflect : has_reflect name
| name.anonymous        := `(name.anonymous)
| (name.mk_string  n s) := `(λ n, name.mk_string  n s).subst (name.reflect n)
| (name.mk_numeral n i) := `(λ n, name.mk_numeral n i).subst (name.reflect n)

meta instance list.reflect {α : Type} [has_reflect α] [reflected α] : has_reflect (list α)
| []     := `([])
| (h::t) := `(λ t, h :: t).subst (list.reflect t)

meta instance punit.reflect : has_reflect punit
| () := `(_)

meta instance bool.reflect : has_reflect bool
| tt := `(_)
| ff := `(_)

meta instance prod.reflect {α β : Type} [has_reflect α] [has_reflect β] [reflected α] [reflected β] : has_reflect (α × β)
| (a, b) := `(_)

meta instance sum.reflect {α β : Type} [has_reflect α] [has_reflect β] [reflected α] [reflected β] : has_reflect (sum α β)
| (sum.inl a) := `(_)
| (sum.inr b) := `(_)

meta instance option.reflect {α : Type} [has_reflect α] [reflected α] : has_reflect (option α)
| none     := `(_)
| (some a) := `(_)

meta instance pos.reflect : has_reflect pos
| {line := l, column := c} := `(_)
