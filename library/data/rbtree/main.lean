/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import data.rbtree.find data.rbtree.insert data.rbtree.min_max
universes u

namespace rbnode
variables {α : Type u} {lt : α → α → Prop}

lemma is_searchable_of_well_formed {t : rbnode α} [is_strict_weak_order α lt] : t.well_formed lt → is_searchable lt t none none :=
begin
  intro h, induction h,
  { constructor, simp [lift] },
  { subst h_n', apply is_searchable_insert, assumption }
end

open color

lemma is_red_black_of_well_formed {t : rbnode α} : t.well_formed lt → ∃ c n, is_red_black t c n :=
begin
  intro h, induction h,
  { existsi black, existsi 0, constructor },
  { cases h_ih with c ih, cases ih with n ih, subst h_n', apply insert_is_red_black, assumption }
end

end rbnode

namespace rbtree
variables {α : Type u} {lt : α → α → Prop}

lemma balanced (t : rbtree α lt) : 2 * t.depth min + 1 ≥ t.depth max :=
begin
  cases t with n p, simp only [depth],
  have := rbnode.is_red_black_of_well_formed p,
  cases this with _ this, cases this with _ this,
  apply rbnode.balanced, assumption
end

lemma not_mem_mk_rbtree : ∀ (a : α), a ∉ mk_rbtree α lt :=
by simp [has_mem.mem, rbtree.mem, rbnode.mem, mk_rbtree]

lemma not_mem_of_empty {t : rbtree α lt} (a : α) : t.empty = tt → a ∉ t :=
by cases t with n p; cases n; simp [empty, has_mem.mem, rbtree.mem, rbnode.mem]

lemma mem_of_mem_of_eqv [is_strict_weak_order α lt] {t : rbtree α lt} {a b : α} : a ∈ t → a ≈[lt] b → b ∈ t :=
begin
  cases t with n p; simp [has_mem.mem, rbtree.mem]; clear p; induction n; simp [rbnode.mem, strict_weak_order.equiv]; intros h₁ h₂; blast_disjs,
  iterate 2 {
    { have : rbnode.mem lt b n_lchild := n_ih_lchild h₁ h₂, simp [this] },
    { simp [incomp_trans_of lt h₂.swap h₁] },
    { have : rbnode.mem lt b n_rchild := n_ih_rchild h₁ h₂, simp [this] } }
end

variables [decidable_rel lt]

lemma insert_ne_mk_rbtree (t : rbtree α lt) (a : α) : t.insert a ≠ mk_rbtree α lt :=
begin cases t with n p, simp [insert, mk_rbtree], intro h, injection h with h', apply rbnode.insert_ne_leaf lt n a h' end

lemma find_correct [is_strict_weak_order α lt] (a : α) (t : rbtree α lt) : a ∈ t ↔ (∃ b, t.find a = some b ∧ a ≈[lt] b) :=
begin cases t, apply rbnode.find_correct, apply rbnode.is_searchable_of_well_formed, assumption end

lemma find_correct_of_total [is_strict_total_order α lt] (a : α) (t : rbtree α lt) : a ∈ t ↔ t.find a = some a :=
iff.intro
  (λ h, match iff.mp (find_correct a t) h with
        | ⟨b, heq, heqv⟩ := by simp [heq, (eq_of_eqv_lt heqv).symm]
        end)
  (λ h, iff.mpr (find_correct a t) ⟨a, ⟨h, refl a⟩⟩)

lemma find_correct_exact [is_strict_total_order α lt] (a : α) (t : rbtree α lt) : mem_exact a t ↔ t.find a = some a :=
begin cases t, apply rbnode.find_correct_exact, apply rbnode.is_searchable_of_well_formed, assumption end

lemma find_insert_of_eqv [is_strict_weak_order α lt] (t : rbtree α lt) {x y} : x ≈[lt] y → (t.insert x).find y = some x :=
begin cases t, intro h, apply rbnode.find_insert_of_eqv lt h, apply rbnode.is_searchable_of_well_formed, assumption end

lemma find_insert [is_strict_weak_order α lt] (t : rbtree α lt) (x) : (t.insert x).find x = some x :=
find_insert_of_eqv t (refl x)

lemma find_insert_of_disj [is_strict_weak_order α lt] {x y : α} (t : rbtree α lt) : lt x y ∨ lt y x → (t.insert x).find y = t.find y :=
begin cases t, intro h, apply rbnode.find_insert_of_disj lt h, apply rbnode.is_searchable_of_well_formed, assumption end

lemma find_insert_of_not_eqv [is_strict_weak_order α lt] {x y : α} (t : rbtree α lt) : ¬ x ≈[lt] y → (t.insert x).find y = t.find y :=
begin cases t, intro h, apply rbnode.find_insert_of_not_eqv lt h, apply rbnode.is_searchable_of_well_formed, assumption end

lemma find_insert_of_ne [is_strict_total_order α lt] {x y : α} (t : rbtree α lt) : x ≠ y → (t.insert x).find y = t.find y :=
begin
  cases t, intro h,
  have : ¬ x ≈[lt] y := λ h', h (eq_of_eqv_lt h'),
  apply rbnode.find_insert_of_not_eqv lt this,
  apply rbnode.is_searchable_of_well_formed, assumption
end

lemma not_mem_of_find_none [is_strict_weak_order α lt] {a : α} {t : rbtree α lt} : t.find a = none → a ∉ t :=
λ h, iff.mpr (not_iff_not_of_iff (find_correct a t)) $
  begin
    intro h,
    cases h with _ h, cases h with h₁ h₂,
    rw [h] at h₁, contradiction
  end

lemma eqv_of_find_some [is_strict_weak_order α lt] {a b : α} {t : rbtree α lt} : t.find a = some b → a ≈[lt] b :=
begin cases t, apply rbnode.eqv_of_find_some, apply rbnode.is_searchable_of_well_formed, assumption end

lemma eq_of_find_some [is_strict_total_order α lt] {a b : α} {t : rbtree α lt} : t.find a = some b → a = b :=
λ h, suffices a ≈[lt] b, from eq_of_eqv_lt this,
     eqv_of_find_some h

lemma mem_of_find_some [is_strict_weak_order α lt] {a b : α} {t : rbtree α lt} : t.find a = some b → a ∈ t :=
λ h, iff.mpr (find_correct a t) ⟨b, ⟨h, eqv_of_find_some h⟩⟩

lemma find_eq_find_of_eqv [is_strict_weak_order α lt] {a b : α} (t : rbtree α lt) : a ≈[lt] b → t.find a = t.find b :=
begin
  cases t, apply rbnode.find_eq_find_of_eqv,
  apply rbnode.is_searchable_of_well_formed, assumption
end

lemma contains_correct [is_strict_weak_order α lt] (a : α) (t : rbtree α lt) : a ∈ t ↔ (t.contains a = tt) :=
begin
  have h := find_correct a t,
  simp [h, contains], apply iff.intro,
  { intro h', cases h' with _ h', cases h', simp [*], simp [option.is_some] },
  { intro h',
    cases heq : find t a with v, simp [heq, option.is_some] at h', contradiction,
    existsi v, simp, apply eqv_of_find_some heq }
end

lemma mem_insert_of_incomp {a b : α} (t : rbtree α lt) : (¬ lt a b ∧ ¬ lt b a) → a ∈ t.insert b :=
begin cases t, apply rbnode.mem_insert_of_incomp end

lemma mem_insert [is_irrefl α lt] : ∀ (a : α) (t : rbtree α lt), a ∈ t.insert a :=
begin intros, apply mem_insert_of_incomp, split; apply irrefl_of lt end

lemma mem_insert_of_equiv {a b : α} (t : rbtree α lt) : a ≈[lt] b → a ∈ t.insert b :=
begin cases t, apply rbnode.mem_insert_of_incomp end

lemma mem_insert_of_mem [is_strict_weak_order α lt] {a : α} {t : rbtree α lt} (b : α) : a ∈ t → a ∈ t.insert b :=
begin cases t, apply rbnode.mem_insert_of_mem end

lemma equiv_or_mem_of_mem_insert [is_strict_weak_order α lt] {a b : α} {t : rbtree α lt} : a ∈ t.insert b → a ≈[lt] b ∨ a ∈ t :=
begin cases t, apply rbnode.equiv_or_mem_of_mem_insert end

lemma incomp_or_mem_of_mem_ins [is_strict_weak_order α lt] {a b : α} {t : rbtree α lt} : a ∈ t.insert b → (¬ lt a b ∧ ¬ lt b a) ∨ a ∈ t :=
equiv_or_mem_of_mem_insert

lemma eq_or_mem_of_mem_ins [is_strict_total_order α lt] {a b : α} {t : rbtree α lt} : a ∈ t.insert b → a = b ∨ a ∈ t :=
λ h, suffices a ≈[lt] b ∨ a ∈ t, by simp [eqv_lt_iff_eq] at this; assumption,
  incomp_or_mem_of_mem_ins h

lemma mem_of_min_eq [is_irrefl α lt] {a : α} {t : rbtree α lt} : t.min = some a → a ∈ t :=
begin cases t, apply rbnode.mem_of_min_eq end

lemma mem_of_max_eq [is_irrefl α lt] {a : α} {t : rbtree α lt} : t.max = some a → a ∈ t :=
begin cases t, apply rbnode.mem_of_max_eq end

lemma eq_leaf_of_min_eq_none [is_strict_weak_order α lt] {t : rbtree α lt} : t.min = none → t = mk_rbtree α lt :=
begin cases t, intro h, congr, apply rbnode.eq_leaf_of_min_eq_none h end

lemma eq_leaf_of_max_eq_none [is_strict_weak_order α lt] {t : rbtree α lt} : t.max = none → t = mk_rbtree α lt :=
begin cases t, intro h, congr, apply rbnode.eq_leaf_of_max_eq_none h end

lemma min_is_minimal [is_strict_weak_order α lt] {a : α} {t : rbtree α lt} : t.min = some a → ∀ {b}, b ∈ t → a ≈[lt] b ∨ lt a b :=
begin cases t, apply rbnode.min_is_minimal, apply rbnode.is_searchable_of_well_formed, assumption end

lemma max_is_maximal [is_strict_weak_order α lt] {a : α} {t : rbtree α lt} : t.max = some a → ∀ {b}, b ∈ t → a ≈[lt] b ∨ lt b a :=
begin cases t, apply rbnode.max_is_maximal, apply rbnode.is_searchable_of_well_formed, assumption end

end rbtree
