/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
prelude
import .basic init.data.nat init.data.list.lemmas
universes u w

namespace array
variables {α : Type u} {β : Type w} {n : nat}

lemma read_eq_read' [inhabited α] (a : array α n) (i : nat) (h : i < n) : read a ⟨i, h⟩ = read' a i :=
by unfold read'; rw [dif_pos h]

lemma write_eq_write' (a : array α n) (i : nat) (h : i < n) (v : α) : write a ⟨i, h⟩ v = write' a i v :=
by unfold write'; rw [dif_pos h]

theorem rev_list_reverse_core (a : array α n) : Π i (h : i ≤ n) (t : list α),
  (a.iterate_aux (λ _ v l, v :: l) i h []).reverse_core t = a.rev_iterate_aux (λ _ v l, v :: l) i h t
| 0     h t := rfl
| (i+1) h t := rev_list_reverse_core i _ _

theorem rev_list_reverse (a : array α n) : a.rev_list.reverse = a.to_list :=
rev_list_reverse_core a _ _ _

theorem to_list_reverse (a : array α n) : a.to_list.reverse = a.rev_list :=
by rw [-rev_list_reverse, list.reverse_reverse]

theorem rev_list_length_aux (a : array α n) (i h) : (a.iterate_aux (λ _ v l, v :: l) i h []).length = i :=
by induction i; simp [*, iterate_aux]

theorem rev_list_length (a : array α n) : a.rev_list.length = n :=
rev_list_length_aux a _ _

theorem to_list_length (a : array α n) : a.to_list.length = n :=
by rw[-rev_list_reverse, list.length_reverse, rev_list_length]

theorem to_list_nth_core (a : array α n) (i : ℕ) (ih : i < n) : Π (j) {jh t h'},
  (∀k tl, j + k = i → list.nth_le t k tl = a.read ⟨i, ih⟩) → (a.rev_iterate_aux (λ _ v l, v :: l) j jh t).nth_le i h' = a.read ⟨i, ih⟩
| 0     _  _ _  al := al i _ $ zero_add _
| (j+1) jh t h' al := to_list_nth_core j $ λk tl hjk,
  show list.nth_le (a.read ⟨j, jh⟩ :: t) k tl = a.read ⟨i, ih⟩, from
  match k, hjk, tl with
  | 0,    e, tl := match i, e, ih with ._, rfl, _ := rfl end
  | k'+1, _, tl := by simp[list.nth_le]; exact al _ _ (by simp [*])
  end

theorem to_list_nth (a : array α n) (i : ℕ) (h h') : list.nth_le a.to_list i h' = a.read ⟨i, h⟩ :=
to_list_nth_core _ _ _ _ (λk tl, absurd tl $ nat.not_lt_zero _)

theorem mem_iff_rev_list_mem_core (a : array α n) (v : α) : Π i (h : i ≤ n),
  (∃ (j : fin n), j.1 < i ∧ read a j = v) ↔ v ∈ a.iterate_aux (λ _ v l, v :: l) i h []
| 0     _ := ⟨λ⟨_, n, _⟩, absurd n $ nat.not_lt_zero _, false.elim⟩
| (i+1) h := let IH := mem_iff_rev_list_mem_core i (le_of_lt h) in
  ⟨λ⟨j, ji1, e⟩, or.elim (lt_or_eq_of_le $ nat.le_of_succ_le_succ ji1)
    (λji, list.mem_cons_of_mem _ $ IH.1 ⟨j, ji, e⟩)
    (λje, by simp[iterate_aux]; apply or.inl; have H : j = ⟨i, h⟩ := fin.eq_of_veq je; rwa [-H, e]),
  λm, begin
    simp[iterate_aux, list.mem] at m,
    cases m with e m',
    exact ⟨⟨i, h⟩, nat.lt_succ_self _, eq.symm e⟩,
    exact let ⟨j, ji, e⟩ := IH.2 m' in
    ⟨j, nat.le_succ_of_le ji, e⟩
  end⟩

theorem mem_iff_rev_list_mem (a : array α n) (v : α) : v ∈ a ↔ v ∈ a.rev_list :=
iff.trans
  (exists_congr $ λj, iff.symm $ show j.1 < n ∧ read a j = v ↔ read a j = v, from and_iff_right j.2)
  (mem_iff_rev_list_mem_core a v _ _)

theorem mem_iff_list_mem (a : array α n) (v : α) : v ∈ a ↔ v ∈ a.to_list :=
by rw -rev_list_reverse; simp[mem_iff_rev_list_mem]

@[simp] def to_list_to_array (a : array α n) : a.to_list.to_array == a :=
have array.mk (λ (v : fin n), list.nth_le (to_list a) (v.val) (eq.rec_on (eq.symm (to_list_length a)) (v.is_lt))) = a, from
match a with ⟨f⟩ := congr_arg array.mk $ funext $ λ⟨i, h⟩, to_list_nth ⟨f⟩ i h _ end,
heq_of_heq_of_eq
  (@eq.drec_on _ _ (λm (e : a.to_list.length = m), (array.mk (λv, a.to_list.nth_le v.1 v.2)) ==
    (@array.mk α m $ λv, a.to_list.nth_le v.1 (eq.rec_on (eq.symm e) v.2))) _ a.to_list_length (heq.refl _)) this

@[simp] def to_array_to_list (l : list α) : l.to_array.to_list = l :=
list.ext_le (to_list_length _) $ λn h1 h2, to_list_nth _ _ _ _

end array
