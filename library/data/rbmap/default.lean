/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import data.rbtree

universes u v

namespace rbmap
variables {α : Type u} {β : Type v} {lt : α → α → Prop}

/- Auxiliary instances -/
private def rbmap_lt_is_swo {α : Type u} {β : Type v} {lt : α → α → Prop} [is_strict_weak_order α lt] : is_strict_weak_order (α × β) (rbmap_lt lt) :=
{ irrefl       := λ _, irrefl_of lt _,
  trans        := λ _ _ _ h₁ h₂, trans_of lt h₁ h₂,
  incomp_trans := λ _ _ _ h₁ h₂, incomp_trans_of lt h₁ h₂ }

private def rbmap_lt_dec {α : Type u} {β : Type v} {lt : α → α → Prop} [h : decidable_rel lt] : decidable_rel (@rbmap_lt α β lt) :=
λ a b, h a.1 b.1

local attribute [instance] rbmap_lt_is_swo rbmap_lt_dec

/- Helper lemmas for reusing rbtree results. -/

private lemma to_rbtree_mem {k : α} {m : rbmap α β lt} : k ∈ m → ∃ v : β, rbtree.mem (k, v) m :=
begin
  cases m with n p; cases n; intros h,
  { exact false.elim h },
  all_goals { existsi n_val.2, exact h }
end

private lemma eqv_entries_of_eqv_keys {k₁ k₂ : α} (v₁ v₂ : β) : k₁ ≈[lt] k₂ → (k₁, v₁) ≈[rbmap_lt lt] (k₂, v₂) :=
id

private lemma eqv_keys_of_eqv_entries {k₁ k₂ : α} {v₁ v₂ : β} : (k₁, v₁) ≈[rbmap_lt lt] (k₂, v₂) → k₁ ≈[lt] k₂ :=
id

private lemma eqv_entries [is_irrefl α lt] (k : α) (v₁ v₂ : β) : (k, v₁) ≈[rbmap_lt lt] (k, v₂) :=
and.intro (irrefl_of lt k) (irrefl_of lt k)

private lemma to_rbmap_mem [is_strict_weak_order α lt] {k : α} {v : β} {m : rbmap α β lt} : rbtree.mem (k, v) m → k ∈ m :=
begin
  cases m with n p; cases n; intros h,
  { exact false.elim h },
  { simp [has_mem.mem, rbmap.mem],
    exact @rbtree.mem_of_mem_of_eqv _ _ _ ⟨rbnode.red_node n_lchild n_val n_rchild, p⟩ _ _ h (eqv_entries _ _ _) },
  { simp [has_mem.mem, rbmap.mem],
    exact @rbtree.mem_of_mem_of_eqv _ _ _ ⟨rbnode.black_node n_lchild n_val n_rchild, p⟩ _ _ h (eqv_entries _ _ _) }
end

private lemma to_rbtree_mem' [is_strict_weak_order α lt] {k : α} {m : rbmap α β lt} (v : β) : k ∈ m → rbtree.mem (k, v) m :=
begin
  intro h,
  cases to_rbtree_mem h with v' hm,
  apply rbtree.mem_of_mem_of_eqv hm,
  apply eqv_entries
end

lemma eq_some_of_to_value_eq_some {e : option (α × β)} {v : β} : to_value e = some v → ∃ k, e = some (k, v) :=
begin
  cases e with val; simp [to_value],
    { cases val, simp, intro h, subst v, constructor, refl }
end

lemma eq_none_of_to_value_eq_none {e : option (α × β)} : to_value e = none → e = none :=
by cases e; simp [to_value]

/- Lemmas -/

lemma not_mem_mk_rbmap : ∀ (k : α), k ∉ mk_rbmap α β lt :=
by simp [has_mem.mem, mk_rbmap, mk_rbtree, rbmap.mem]

lemma not_mem_of_empty {m : rbmap α β lt} (k : α) : m.empty = tt → k ∉ m :=
by cases m with n p; cases n; simp [has_mem.mem, mk_rbmap, mk_rbtree, rbmap.mem, rbmap.empty, rbtree.empty]

variables [decidable_rel lt]

lemma not_mem_of_find_entry_none [is_strict_weak_order α lt] {k : α} {m : rbmap α β lt} : m.find_entry k = none → k ∉ m :=
begin
  cases m with t p, cases t; simp [find_entry],
  { intros, simp [has_mem.mem, rbmap.mem] },
  all_goals { intro h, exact rbtree.not_mem_of_find_none h, }
end

lemma not_mem_of_find_none [is_strict_weak_order α lt] {k : α} {m : rbmap α β lt} : m.find k = none → k ∉ m :=
begin
  simp [find], intro h,
  have := eq_none_of_to_value_eq_none h,
  exact not_mem_of_find_entry_none this
end

lemma mem_of_find_entry_some [is_strict_weak_order α lt] {k₁ : α} {e : α × β} {m : rbmap α β lt} : m.find_entry k₁ = some e → k₁ ∈ m :=
begin
  cases m with t p, cases t; simp [find_entry],
  all_goals { intro h, exact rbtree.mem_of_find_some h }
end

lemma mem_of_find_some [is_strict_weak_order α lt] {k : α} {v : β} {m : rbmap α β lt} : m.find k = some v → k ∈ m :=
begin
  simp [find], intro h,
  have := eq_some_of_to_value_eq_some h,
  cases this with _ he,
  exact mem_of_find_entry_some he
end

lemma find_entry_eq_find_entry_of_eqv [is_strict_weak_order α lt] {m : rbmap α β lt} {k₁ k₂ : α} : k₁ ≈[lt] k₂ → m.find_entry k₁ = m.find_entry k₂ :=
begin
  intro h, cases m with t p, cases t; simp [find_entry],
  all_goals { apply rbtree.find_eq_find_of_eqv, apply eqv_entries_of_eqv_keys, assumption }
end

lemma find_eq_find_of_eqv [is_strict_weak_order α lt] {k₁ k₂ : α} (m : rbmap α β lt) : k₁ ≈[lt] k₂ → m.find k₁ = m.find k₂ :=
begin intro h, simp [find], apply congr_arg, apply find_entry_eq_find_entry_of_eqv, assumption end

lemma find_entry_correct [is_strict_weak_order α lt] (k : α) (m : rbmap α β lt) : k ∈ m ↔ (∃ e, m.find_entry k = some e ∧ k ≈[lt] e.1) :=
begin
  apply iff.intro; cases m with t p,
  { intro h,
    have h   := to_rbtree_mem h, cases h with v h₁,
    have hex := iff.mp (rbtree.find_correct _ _) h₁, cases hex with e h₂,
    existsi e, cases t; simp [find_entry] at ⊢ h₂,
    { simp [rbtree.find, rbnode.find] at h₂, cases h₂ },
    { cases h₂ with h₂₁ h₂₂, split,
      { have := rbtree.find_eq_find_of_eqv ⟨rbnode.red_node t_lchild t_val t_rchild, p⟩ (eqv_entries k v t_val.2),
        rw [←this], exact h₂₁ },
      { cases e, apply eqv_keys_of_eqv_entries h₂₂ } },
    { cases h₂ with h₂₁ h₂₂, split,
      { have := rbtree.find_eq_find_of_eqv ⟨rbnode.black_node t_lchild t_val t_rchild, p⟩ (eqv_entries k v t_val.2),
        rw [←this], exact h₂₁ },
      { cases e, apply eqv_keys_of_eqv_entries h₂₂ } } },
  { intro h, cases h with e h,
    cases h with h₁ h₂, cases t; simp [find_entry] at h₁,
    { contradiction },
    all_goals { exact to_rbmap_mem (rbtree.mem_of_find_some h₁) } }
end

lemma eqv_of_find_entry_some [is_strict_weak_order α lt] {k₁ k₂ : α} {v : β} {m : rbmap α β lt} : m.find_entry k₁ = some (k₂, v) → k₁ ≈[lt] k₂ :=
begin
  cases m with t p, cases t; simp [find_entry],
  all_goals { intro h, exact eqv_keys_of_eqv_entries (rbtree.eqv_of_find_some h) }
end

lemma eq_of_find_entry_some [is_strict_total_order α lt] {k₁ k₂ : α} {v : β} {m : rbmap α β lt} : m.find_entry k₁ = some (k₂, v) → k₁ = k₂ :=
λ h, suffices k₁ ≈[lt] k₂, from eq_of_eqv_lt this,
     eqv_of_find_entry_some h

lemma find_correct [is_strict_weak_order α lt] (k : α) (m : rbmap α β lt) : k ∈ m ↔ ∃ v, m.find k = some v :=
begin
  apply iff.intro,
  { intro h,
    have := iff.mp (find_entry_correct k m) h,
    cases this with e h, cases h with h₁ h₂,
    existsi e.2, simp [find, h₁, to_value] },
  { intro h,
    cases h with v h,
    simp [find] at h,
    have h := eq_some_of_to_value_eq_some h,
    cases h with k' h,
    have heqv := eqv_of_find_entry_some h,
    exact iff.mpr (find_entry_correct k m) ⟨(k', v), ⟨h, heqv⟩⟩ }
end

lemma constains_correct [is_strict_weak_order α lt] (k : α) (m : rbmap α β lt) : k ∈ m ↔ m.contains k = tt :=
begin
   apply iff.intro,
   { intro h,
     have h := iff.mp (find_entry_correct k m) h,
     cases h with e h, cases h with h₁ h₂,
     simp [contains, h₁, option.is_some] },
   { simp [contains],
     intro h,
     generalize he : find_entry m k = e,
     cases e,
       { simp [he, option.is_some] at h, contradiction },
       { exact mem_of_find_entry_some he } }
end

lemma mem_of_mem_of_eqv [is_strict_weak_order α lt] {m : rbmap α β lt} {k₁ k₂ : α} : k₁ ∈ m → k₁ ≈[lt] k₂ → k₂ ∈ m :=
begin
  intros h₁ h₂,
  have h₁ := to_rbtree_mem h₁, cases h₁ with v h₁,
  exact to_rbmap_mem (rbtree.mem_of_mem_of_eqv h₁ (eqv_entries_of_eqv_keys v v h₂))
end

lemma mem_insert_of_incomp [is_strict_weak_order α lt] {k₁ k₂ : α} (m : rbmap α β lt) (v : β) : (¬ lt k₁ k₂ ∧ ¬ lt k₂ k₁) → k₁ ∈ m.insert k₂ v :=
λ h, to_rbmap_mem (rbtree.mem_insert_of_incomp m (eqv_entries_of_eqv_keys v v h))

lemma mem_insert [is_strict_weak_order α lt] (k : α) (m : rbmap α β lt) (v : β) : k ∈ m.insert k v :=
to_rbmap_mem (rbtree.mem_insert (k, v) m)

lemma mem_insert_of_equiv [is_strict_weak_order α lt] {k₁ k₂ : α} (m : rbmap α β lt) (v : β) : k₁ ≈[lt] k₂ → k₁ ∈ m.insert k₂ v :=
mem_insert_of_incomp m v

lemma mem_insert_of_mem [is_strict_weak_order α lt] {k₁ : α} {m : rbmap α β lt} (k₂ : α) (v : β) : k₁ ∈ m → k₁ ∈ m.insert k₂ v :=
λ h, to_rbmap_mem (rbtree.mem_insert_of_mem (k₂, v) (to_rbtree_mem' v h))

lemma equiv_or_mem_of_mem_insert [is_strict_weak_order α lt] {k₁ k₂ : α} {v : β} {m : rbmap α β lt} : k₁ ∈ m.insert k₂ v → k₁ ≈[lt] k₂ ∨ k₁ ∈ m :=
λ h, or.elim (rbtree.equiv_or_mem_of_mem_insert (to_rbtree_mem' v h))
  (λ h, or.inl (eqv_keys_of_eqv_entries h))
  (λ h, or.inr (to_rbmap_mem h))

lemma incomp_or_mem_of_mem_ins [is_strict_weak_order α lt] {k₁ k₂ : α} {v : β} {m : rbmap α β lt} : k₁ ∈ m.insert k₂ v → (¬ lt k₁ k₂ ∧ ¬ lt k₂ k₁) ∨ k₁ ∈ m :=
equiv_or_mem_of_mem_insert

lemma eq_or_mem_of_mem_ins [is_strict_total_order α lt] {k₁ k₂ : α} {v : β} {m : rbmap α β lt} : k₁ ∈ m.insert k₂ v → k₁ = k₂ ∨ k₁ ∈ m :=
λ h, suffices k₁ ≈[lt] k₂ ∨ k₁ ∈ m, by simp [eqv_lt_iff_eq] at this; assumption,
  incomp_or_mem_of_mem_ins h

lemma find_entry_insert_of_eqv [is_strict_weak_order α lt] (m : rbmap α β lt) {k₁ k₂ : α} (v : β) : k₁ ≈[lt] k₂ → (m.insert k₁ v).find_entry k₂ = some (k₁, v) :=
begin
  intro h,
  generalize h₁ : m.insert k₁ v = m',
  cases m' with t p, cases t,
  { have := mem_insert k₁ m v, rw [h₁] at this, apply absurd this, apply not_mem_mk_rbmap },
  all_goals { simp [find_entry], rw [←h₁, insert], apply rbtree.find_insert_of_eqv, apply eqv_entries_of_eqv_keys _ _ h }
end

lemma find_entry_insert [is_strict_weak_order α lt] (m : rbmap α β lt) (k : α) (v : β) : (m.insert k v).find_entry k = some (k, v) :=
find_entry_insert_of_eqv m v (refl k)

lemma find_insert_of_eqv [is_strict_weak_order α lt] (m : rbmap α β lt) {k₁ k₂ : α} (v : β) : k₁ ≈[lt] k₂ → (m.insert k₁ v).find k₂ = some v :=
begin
  intro h,
  have := find_entry_insert_of_eqv m v h,
  simp [find, this, to_value]
end

lemma find_insert [is_strict_weak_order α lt] (m : rbmap α β lt) (k : α) (v : β) : (m.insert k v).find k = some v :=
find_insert_of_eqv m v (refl k)

lemma find_entry_insert_of_disj [is_strict_weak_order α lt] {k₁ k₂ : α} (m : rbmap α β lt) (v : β) : lt k₁ k₂ ∨ lt k₂ k₁ → (m.insert k₁ v).find_entry k₂ = m.find_entry k₂ :=
begin
  intro h,
  have h' : ∀ {v₁ v₂ : β}, (rbmap_lt lt) (k₁, v₁) (k₂, v₂) ∨ (rbmap_lt lt) (k₂, v₂) (k₁, v₁) := λ _ _, h,
  generalize h₁ : m = m₁,
  generalize h₂ : insert m₁ k₁ v = m₂,
  rw [←h₁] at h₂ ⊢, rw [←h₂],
  cases m₁ with t₁ p₁; cases t₁; cases m₂ with t₂ p₂; cases t₂,
  { rw [h₂, h₁] },
  iterate 2 {
    rw [h₂],
    conv { to_lhs, simp [find_entry] },
    rw [←h₂, insert, rbtree.find_insert_of_disj _ h', h₁],
    refl },
  any_goals { simp [insert] at h₂,
    exact absurd h₂ (rbtree.insert_ne_mk_rbtree m (k₁, v)) },
  any_goals {
    rw [h₂, h₁], simp [find_entry], rw [←h₂, ←h₁, insert, rbtree.find_insert_of_disj _ h'],
    apply rbtree.find_eq_find_of_eqv, apply eqv_entries }
end

lemma find_entry_insert_of_not_eqv [is_strict_weak_order α lt] {k₁ k₂ : α} (m : rbmap α β lt) (v : β) : ¬ k₁ ≈[lt] k₂ → (m.insert k₁ v).find_entry k₂ = m.find_entry k₂ :=
begin
  intro hn,
  have he : lt k₁ k₂ ∨ lt k₂ k₁, {
    simp [strict_weak_order.equiv, decidable.not_and_iff_or_not, decidable.not_not_iff] at hn,
    assumption },
  apply find_entry_insert_of_disj _ _ he
end

lemma find_entry_insert_of_ne [is_strict_total_order α lt] {k₁ k₂ : α} (m : rbmap α β lt) (v : β) : k₁ ≠ k₂ → (m.insert k₁ v).find_entry k₂ = m.find_entry k₂ :=
begin
  intro h,
  have : ¬ k₁ ≈[lt] k₂ := λ h', h (eq_of_eqv_lt h'),
  apply find_entry_insert_of_not_eqv _ _ this
end

lemma find_insert_of_disj [is_strict_weak_order α lt] {k₁ k₂ : α} (m : rbmap α β lt) (v : β) : lt k₁ k₂ ∨ lt k₂ k₁ → (m.insert k₁ v).find k₂ = m.find k₂ :=
begin intro h, have := find_entry_insert_of_disj m v h, simp [find, this] end

lemma find_insert_of_not_eqv [is_strict_weak_order α lt] {k₁ k₂ : α} (m : rbmap α β lt) (v : β) : ¬ k₁ ≈[lt] k₂ → (m.insert k₁ v).find k₂ = m.find k₂ :=
begin intro h, have := find_entry_insert_of_not_eqv m v h, simp [find, this] end

lemma find_insert_of_ne [is_strict_total_order α lt] {k₁ k₂ : α} (m : rbmap α β lt) (v : β) : k₁ ≠ k₂ → (m.insert k₁ v).find k₂ = m.find k₂ :=
begin intro h, have := find_entry_insert_of_ne m v h, simp [find, this] end

lemma mem_of_min_eq [is_strict_total_order α lt] {k : α} {v : β} {m : rbmap α β lt} : m.min = some (k, v) → k ∈ m :=
λ h, to_rbmap_mem (rbtree.mem_of_min_eq h)

lemma mem_of_max_eq [is_strict_total_order α lt] {k : α} {v : β} {m : rbmap α β lt} : m.max = some (k, v) → k ∈ m :=
λ h, to_rbmap_mem (rbtree.mem_of_max_eq h)

lemma eq_leaf_of_min_eq_none [is_strict_weak_order α lt] {m : rbmap α β lt} : m.min = none → m = mk_rbmap α β lt :=
rbtree.eq_leaf_of_min_eq_none

lemma eq_leaf_of_max_eq_none [is_strict_weak_order α lt] {m : rbmap α β lt} : m.max = none → m = mk_rbmap α β lt :=
rbtree.eq_leaf_of_max_eq_none

lemma min_is_minimal [is_strict_weak_order α lt] {k : α} {v : β} {m : rbmap α β lt} : m.min = some (k, v) → ∀ {k'}, k' ∈ m → k ≈[lt] k' ∨ lt k k' :=
λ h k' hm, or.elim (rbtree.min_is_minimal h (to_rbtree_mem' v hm))
  (λ h, or.inl (eqv_keys_of_eqv_entries h))
  (λ h, or.inr h)

lemma max_is_maximal [is_strict_weak_order α lt] {k : α} {v : β} {m : rbmap α β lt} : m.max = some (k, v) → ∀ {k'}, k' ∈ m → k ≈[lt] k' ∨ lt k' k :=
λ h k' hm, or.elim (rbtree.max_is_maximal h (to_rbtree_mem' v hm))
  (λ h, or.inl (eqv_keys_of_eqv_entries h))
  (λ h, or.inr h)

lemma min_is_minimal_of_total [is_strict_total_order α lt] {k : α} {v : β} {m : rbmap α β lt} : m.min = some (k, v) → ∀ {k'}, k' ∈ m → k = k' ∨ lt k k' :=
λ h k' hm,
  match min_is_minimal h hm with
  | or.inl h := or.inl (eq_of_eqv_lt h)
  | or.inr h := or.inr h
  end

lemma max_is_maximal_of_total [is_strict_total_order α lt] {k : α} {v : β} {m : rbmap α β lt} : m.max = some (k, v) → ∀ {k'}, k' ∈ m → k = k' ∨ lt k' k :=
λ h k' hm,
  match max_is_maximal h hm with
  | or.inl h := or.inl (eq_of_eqv_lt h)
  | or.inr h := or.inr h
  end

end rbmap
