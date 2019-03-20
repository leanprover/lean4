/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.repr

universes u v

inductive Ordering
| lt | Eq | gt

instance : HasRepr Ordering :=
⟨(λ s, match s with | Ordering.lt := "lt" | Ordering.Eq := "Eq" | Ordering.gt := "gt")⟩

namespace Ordering
def swap : Ordering → Ordering
| lt := gt
| Eq := Eq
| gt := lt

@[inline] def orElse : Ordering → Ordering → Ordering
| lt _ := lt
| Eq o := o
| gt _ := gt

theorem swapSwap : ∀ (o : Ordering), o.swap.swap = o
| lt := rfl
| Eq := rfl
| gt := rfl
end Ordering

@[inline] def cmpUsing {α : Type u} (lt : α → α → Prop) [decidableRel lt] (a b : α) : Ordering :=
if lt a b      then Ordering.lt
else if lt b a then Ordering.gt
else                Ordering.Eq

def cmp {α : Type u} [HasLt α] [decidableRel ((<) : α → α → Prop)] (a b : α) : Ordering :=
cmpUsing (<) a b

instance : DecidableEq Ordering :=
{decEq := λ a b,
  match a with
  | Ordering.lt :=
    (match b with
     | Ordering.lt := isTrue rfl
     | Ordering.Eq := isFalse (λ h, Ordering.noConfusion h)
     | Ordering.gt := isFalse (λ h, Ordering.noConfusion h))
  | Ordering.Eq :=
    (match b with
     | Ordering.lt := isFalse (λ h, Ordering.noConfusion h)
     | Ordering.Eq := isTrue rfl
     | Ordering.gt := isFalse (λ h, Ordering.noConfusion h))
  | Ordering.gt :=
    match b with
    | Ordering.lt := isFalse (λ h, Ordering.noConfusion h)
    | Ordering.Eq := isFalse (λ h, Ordering.noConfusion h)
    | Ordering.gt := isTrue rfl}
