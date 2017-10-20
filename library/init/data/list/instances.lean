/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.list.lemmas
import init.meta.mk_dec_eq_instance
open list

universes u v

local attribute [simp] join ret

instance : monad list :=
{pure := @list.ret, bind := @list.bind,
 id_map := begin
   intros _ xs, induction xs with x xs ih,
   { refl },
   { dsimp [function.comp] at ih, dsimp [function.comp], simp [*] }
 end,
 pure_bind := by simp_intros,
 bind_assoc := begin
   intros _ _ _ xs _ _, induction xs,
   { refl },
   { simp [*] }
 end}

instance : alternative list :=
{ list.monad with
  failure := @list.nil,
  orelse  := @list.append }

instance {α : Type u} [decidable_eq α] : decidable_eq (list α) :=
by tactic.mk_dec_eq_instance

namespace list

variables {α β : Type u} (p : α → Prop) [decidable_pred p]

instance bin_tree_to_list : has_coe (bin_tree α) (list α) :=
⟨bin_tree.to_list⟩

instance decidable_bex : ∀ (l : list α), decidable (∃ x ∈ l, p x)
| [] := is_false (by simp)
| (x::xs) := by simp; have := decidable_bex xs; apply_instance

instance decidable_ball (l : list α) : decidable (∀ x ∈ l, p x) :=
if h : ∃ x ∈ l, ¬ p x then
  is_false $ let ⟨x, h, np⟩ := h in λ al, np (al x h)
else
  is_true $ λ x hx, if h' : p x then h' else false.elim $ h ⟨x, hx, h'⟩

end list
