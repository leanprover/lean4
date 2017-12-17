/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.list.lemmas
import init.meta.mk_dec_eq_instance init.category.lawful
open list

universes u v

local attribute [simp] join list.ret

instance : monad list :=
{ pure := @list.ret, map := @list.map, bind := @list.bind }

instance : is_lawful_monad list :=
{ bind_pure_comp_eq_map := by intros; induction x; simp [*, (<$>), pure] at *,
  id_map := @list.map_id,
  pure_bind := by intros; simp [pure],
  bind_assoc := by intros; induction x; simp * }

instance : alternative list :=
{ failure := @list.nil,
  orelse  := @list.append,
  ..list.monad }

namespace list

variables {α β : Type u} (p : α → Prop) [decidable_pred p]

instance bin_tree_to_list : has_coe (bin_tree α) (list α) :=
⟨bin_tree.to_list⟩

instance decidable_bex : ∀ (l : list α), decidable (∃ x ∈ l, p x)
| []      := is_false (by simp)
| (x::xs) :=
  if h₁ : p x
  then is_true ⟨x, mem_cons_self _ _, h₁⟩
  else match decidable_bex xs with
       | is_true h₂  := is_true
          begin
            cases h₂ with y h, cases h with hm hp,
            exact ⟨y, mem_cons_of_mem _ hm, hp⟩
          end
       | is_false h₂ := is_false
           begin
             intro h, cases h with y h, cases h with hm hp,
             cases eq_or_mem_of_mem_cons hm,
             { rw [h] at hp, contradiction },
             { refine absurd _ h₂,
               exact ⟨y, h, hp⟩ }
           end
       end

instance decidable_ball (l : list α) : decidable (∀ x ∈ l, p x) :=
if h : ∃ x ∈ l, ¬ p x then
  is_false $ let ⟨x, h, np⟩ := h in λ al, np (al x h)
else
  is_true $ λ x hx, if h' : p x then h' else false.elim $ h ⟨x, hx, h'⟩

end list
