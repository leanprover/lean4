/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.repr init.data.prod init.data.sum.basic

universes u v

inductive ordering
| lt | eq | gt

namespace ordering
def swap : ordering → ordering
| lt := gt
| eq := eq
| gt := lt

@[inline] def or_else : ordering → ordering → ordering
| lt _ := lt
| eq o := o
| gt _ := gt

theorem swap_swap : ∀ (o : ordering), o.swap.swap = o
| lt := rfl
| eq := rfl
| gt := rfl
end ordering

open ordering

instance : has_repr ordering :=
⟨(λ s, match s with | ordering.lt := "lt" | ordering.eq := "eq" | ordering.gt := "gt" end)⟩

class has_cmp (α : Type u) :=
(cmp : α → α → ordering)

def cmp_of_lt {α : Type u} [has_lt α] [decidable_rel ((<) : α → α → Prop)] (a b : α) : ordering :=
if      a < b then ordering.lt
else if b < a then ordering.gt
else               ordering.eq

instance has_cmp_of_lt {α : Type u} [has_lt α] [decidable_rel ((<) : α → α → Prop)] : has_cmp α :=
⟨cmp_of_lt⟩

/- Remark: this function has a VM builtin efficient implementation. -/
protected def string.cmp (s1 s2 : string) : ordering :=
cmp_of_lt s1 s2

instance : has_cmp string :=
⟨string.cmp⟩

export has_cmp (cmp)

section cmp_relations
variables {α : Type u} [has_cmp α]

@[reducible] def cmp_lt (a b : α) : Prop :=
cmp a b = ordering.lt

@[reducible] def cmp_eq (a b : α) : Prop :=
cmp a b = ordering.eq

@[reducible] def cmp_gt (a b : α) : Prop :=
cmp a b = ordering.gt

infix ` <_cmp `:50 := cmp_lt
infix ` =_cmp `:50 := cmp_eq
infix ` >_cmp `:50 := cmp_gt

end cmp_relations
