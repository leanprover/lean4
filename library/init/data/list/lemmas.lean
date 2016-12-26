/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn
-/
prelude
import init.data.list.basic init.function

universe variables u v
variables {α : Type u} {β : Type v}

namespace list

lemma append_nil (s : list α) : [] ++ s = s :=
rfl

lemma append_cons (x : α) (s t : list α) : (x::s) ++ t = x::(s ++ t) :=
rfl

theorem map_nil (f : α → β) : map f [] = [] :=
rfl

theorem map_cons (f : α → β) (a : α) (l : list α) : map f (a :: l) = f a :: map f l :=
rfl

theorem length_nil : length (@nil α) = 0 :=
rfl

theorem length_cons (x : α) (t : list α) : length (x::t) = length t + 1 :=
rfl

theorem mem_nil_iff (a : α) : a ∈ [] ↔ false :=
iff.rfl

theorem not_mem_nil (a : α) : a ∉ [] :=
iff.mp $ mem_nil_iff a

theorem mem_cons_self (a : α) (l : list α) : a ∈ a :: l :=
or.inl rfl

theorem eq_nil_of_forall_not_mem : ∀ {l : list α}, (∀ a, a ∉ l) → l = nil
| []        := assume h, rfl
| (b :: l') := assume h, absurd (mem_cons_self b l') (h b)

theorem mem_cons_of_mem (y : α) {a : α} {l : list α} : a ∈ l → a ∈ y :: l :=
assume H, or.inr H

theorem mem_cons_iff (a y : α) (l : list α) : a ∈ y::l ↔ (a = y ∨ a ∈ l) :=
iff.rfl

theorem eq_or_mem_of_mem_cons {a y : α} {l : list α} : a ∈ y::l → a = y ∨ a ∈ l :=
assume h, h

theorem nth_zero (a : α) (l : list α) : nth (a :: l) 0 = some a :=
rfl

theorem nth_succ (a : α) (l : list α) (n : nat) : nth (a::l) (nat.succ n) = nth l n :=
rfl

end list
