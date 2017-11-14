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

instance : has_repr ordering :=
⟨(λ s, match s with | ordering.lt := "lt" | ordering.eq := "eq" | ordering.gt := "gt" end)⟩

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

def cmp_using {α : Type u} (lt : α → α → Prop) [decidable_rel lt] (a b : α) : ordering :=
if lt a b      then ordering.lt
else if lt b a then ordering.gt
else                ordering.eq

def cmp {α : Type u} [has_lt α] [decidable_rel ((<) : α → α → Prop)] (a b : α) : ordering :=
cmp_using (<) a b

instance : decidable_eq ordering :=
λ a b,
  match a with
  | ordering.lt :=
    match b with
    | ordering.lt := is_true rfl
    | ordering.eq := is_false (λ h, ordering.no_confusion h)
    | ordering.gt := is_false (λ h, ordering.no_confusion h)
    end
  | ordering.eq :=
    match b with
    | ordering.lt := is_false (λ h, ordering.no_confusion h)
    | ordering.eq := is_true rfl
    | ordering.gt := is_false (λ h, ordering.no_confusion h)
    end
  | ordering.gt :=
    match b with
    | ordering.lt := is_false (λ h, ordering.no_confusion h)
    | ordering.eq := is_false (λ h, ordering.no_confusion h)
    | ordering.gt := is_true rfl
    end
  end
