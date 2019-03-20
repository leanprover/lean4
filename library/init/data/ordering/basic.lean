/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.repr

universes u v

inductive ordering
| lt | eq | gt

instance : hasRepr ordering :=
⟨(λ s, match s with | ordering.lt := "lt" | ordering.eq := "eq" | ordering.gt := "gt")⟩

namespace ordering
def swap : ordering → ordering
| lt := gt
| eq := eq
| gt := lt

@[inline] def orElse : ordering → ordering → ordering
| lt _ := lt
| eq o := o
| gt _ := gt

theorem swapSwap : ∀ (o : ordering), o.swap.swap = o
| lt := rfl
| eq := rfl
| gt := rfl
end ordering

@[inline] def cmpUsing {α : Type u} (lt : α → α → Prop) [decidableRel lt] (a b : α) : ordering :=
if lt a b      then ordering.lt
else if lt b a then ordering.gt
else                ordering.eq

def cmp {α : Type u} [hasLt α] [decidableRel ((<) : α → α → Prop)] (a b : α) : ordering :=
cmpUsing (<) a b

instance : decidableEq ordering :=
{decEq := λ a b,
  match a with
  | ordering.lt :=
    (match b with
     | ordering.lt := isTrue rfl
     | ordering.eq := isFalse (λ h, ordering.noConfusion h)
     | ordering.gt := isFalse (λ h, ordering.noConfusion h))
  | ordering.eq :=
    (match b with
     | ordering.lt := isFalse (λ h, ordering.noConfusion h)
     | ordering.eq := isTrue rfl
     | ordering.gt := isFalse (λ h, ordering.noConfusion h))
  | ordering.gt :=
    match b with
    | ordering.lt := isFalse (λ h, ordering.noConfusion h)
    | ordering.eq := isFalse (λ h, ordering.noConfusion h)
    | ordering.gt := isTrue rfl}
