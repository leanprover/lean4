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
  { simp [*, cons_bind] }
end
end

local attribute [simp] nil_bind cons_bind append_bind

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

instance : decidable_eq string :=
by tactic.mk_dec_eq_instance

namespace list

variables {α β : Type u} (p : α → Prop) [decidable_pred p]

lemma mem_bind_iff {b : β} {l : list α} {f : α → list β} : b ∈ l >>= f ↔ ∃ a ∈ l, b ∈ f a :=
iff.trans mem_join_iff
  ⟨λ ⟨l', h1, h2⟩, let ⟨a, al, fa⟩ := exists_of_mem_map h1 in ⟨a, al, fa.symm ▸ h2⟩,
  λ ⟨a, al, bfa⟩, ⟨f a, mem_map _ al, bfa⟩⟩

lemma exists_of_mem_bind {b : β} {l : list α} {f : α → list β} : b ∈ l >>= f → ∃ a ∈ l, b ∈ f a :=
mem_bind_iff.1

lemma mem_bind {b : β} {l : list α} {f : α → list β} {a} (al : a ∈ l) (h : b ∈ f a) : b ∈ l >>= f :=
mem_bind_iff.2 ⟨a, al, h⟩

instance decidable_bex : ∀ (l : list α), decidable (∃ x ∈ l, p x)
| [] := is_false (by intro; cases a; cases a_1; cases a_1)
| (x::xs) :=
  if hx : p x then
    is_true ⟨x, or.inl rfl, hx⟩
  else
    match decidable_bex xs with
    | is_true  hxs := is_true $ begin
        cases hxs with x' hx', cases hx' with hx' hpx',
        existsi x', existsi (or.inr hx'), assumption
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

instance decidable_prefix [decidable_eq α] : ∀ (l₁ l₂ : list α), decidable (l₁ <+: l₂)
| []      l₂ := is_true ⟨l₂, rfl⟩
| (a::l₁) [] := is_false $ λ⟨t, te⟩, list.no_confusion te
| (a::l₁) (b::l₂) :=
  if h : a = b then
    decidable_of_decidable_of_iff (decidable_prefix l₁ l₂) $ by rw [← h]; exact
      ⟨λ⟨t, te⟩, ⟨t, by rw [← te]; refl⟩,
       λ⟨t, te⟩, list.no_confusion te (λ_ te, ⟨t, te⟩)⟩
  else
    is_false $ λ⟨t, te⟩, list.no_confusion te $ λh', absurd h' h

-- Alternatively, use mem_tails
instance decidable_suffix [decidable_eq α] : ∀ (l₁ l₂ : list α), decidable (l₁ <:+ l₂)
| []      l₂ := is_true ⟨l₂, append_nil _⟩
| (a::l₁) [] := is_false $ λ⟨t, te⟩, absurd te $
                append_ne_nil_of_ne_nil_right _ _ $ λh, list.no_confusion h
| l₁      l₂ := let len1 := length l₁, len2 := length l₂ in
  if hl : len1 ≤ len2 then
    if he : drop (len2 - len1) l₂ = l₁ then is_true $
      ⟨take (len2 - len1) l₂, by rw [← he, take_append_drop]⟩
    else is_false $
      suffices length l₁ ≤ length l₂ → l₁ <:+ l₂ → drop (length l₂ - length l₁) l₂ = l₁,
        from λsuf, he (this hl suf),
      λ hl ⟨t, te⟩, and.right $
        append_right_inj (eq.trans (take_append_drop (length l₂ - length l₁) l₂) te.symm) $
        by simp; exact nat.sub_sub_self hl
  else is_false $ λ⟨t, te⟩, hl $
    show length l₁ ≤ length l₂, by rw [← te, length_append]; apply nat.le_add_left

instance decidable_infix [decidable_eq α] : ∀ (l₁ l₂ : list α), decidable (l₁ <:+: l₂)
| []      l₂ := is_true ⟨[], l₂, rfl⟩
| (a::l₁) [] := is_false $ λ⟨s, t, te⟩, absurd te $ append_ne_nil_of_ne_nil_left _ _ $
                append_ne_nil_of_ne_nil_right _ _ $ λh, list.no_confusion h
| l₁      l₂ := decidable_of_decidable_of_iff (list.decidable_bex (λt, l₁ <+: t) (tails l₂)) $
  by refine (exists_congr (λt, _)).trans (infix_iff_prefix_suffix _ _).symm;
     exact ⟨λ⟨h1, h2⟩, ⟨h2, (mem_tails _ _).1 h1⟩, λ⟨h2, h1⟩, ⟨(mem_tails _ _).2 h1, h2⟩⟩

instance decidable_sublist [decidable_eq α] : ∀ (l₁ l₂ : list α), decidable (l₁ <+ l₂)
| []      l₂      := is_true $ nil_sublist _
| (a::l₁) []      := is_false $ λh, list.no_confusion $ eq_nil_of_sublist_nil h
| (a::l₁) (b::l₂) :=
  if h : a = b then
    decidable_of_decidable_of_iff (decidable_sublist l₁ l₂) $
      by rw [← h]; exact ⟨cons_sublist_cons _, sublist_of_cons_sublist_cons⟩
  else decidable_of_decidable_of_iff (decidable_sublist (a::l₁) l₂)
    ⟨sublist_cons_of_sublist _, λs, match a, l₁, s, h with
    | a, l₁, sublist.cons ._ ._ ._ s', h := s'
    | ._, ._, sublist.cons2 t ._ ._ s', h := absurd rfl h
    end⟩

end list
