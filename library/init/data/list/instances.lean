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

local attribute [simp] map join ret list.append append_nil

section
variables {α : Type u} {β : Type v} (x : α) (xs ys : list α) (f : α → list β)

private lemma nil_bind : list.bind nil f = nil :=
by simp [list.bind]

private lemma cons_bind : list.bind (x :: xs) f = f x ++ list.bind xs f :=
by simp [list.bind]

private lemma append_bind : list.bind (xs ++ ys) f = list.bind xs f ++ list.bind ys f :=
begin
  induction xs,
  { refl },
  { simph [cons_bind] }
end
end

local attribute [simp] nil_bind cons_bind append_bind

instance : monad list :=
{pure := @list.ret, bind := @list.bind,
 id_map := begin
   intros _ xs, induction xs with x xs ih,
   { refl },
   { dsimp at ih, dsimp, simph }
 end,
 pure_bind := by simp_intros,
 bind_assoc := begin
   intros _ _ _ xs _ _, induction xs,
   { refl },
   { simph }
 end}

instance : alternative list :=
{ list.monad with
  failure := @list.nil,
  orelse  := @list.append }

instance {α : Type u} [decidable_eq α] : decidable_eq (list α) :=
by tactic.mk_dec_eq_instance

instance : decidable_eq string :=
list.decidable_eq

namespace list

variables {α : Type u} (p : α → Prop) [decidable_pred p]

instance decidable_bex : ∀ (l : list α), decidable (∃ x ∈ l, p x)
| [] := is_false (by intro; cases a; cases a_2; cases a)
| (x::xs) :=
  if hx : p x then
    is_true ⟨x, or.inl rfl, hx⟩
  else
    match decidable_bex xs with
    | is_true  hxs := is_true $ begin
        cases hxs with x' hx', cases hx' with hx' hpx',
        existsi x', existsi (or.inr hx'), assumption, exact x' = x
      end
    | is_false hxs := is_false $ begin
        intro hxxs, cases hxxs with x' hx', cases hx' with hx' hpx',
        cases hx', cc,
        apply hxs, existsi x', existsi a, assumption
      end
    end

instance decidable_ball (l : list α) : decidable (∀ x ∈ l, p x) :=
if h : ∃ x ∈ l, ¬ p x then
  is_false $ begin cases h with x h, cases h with hx h, intro h', apply h, apply h', assumption end
else
  is_true $ λ x hx, if h' : p x then h' else false.elim $ h ⟨x, hx, h'⟩

end list
