/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
prelude
import Init.Data.List.Pairwise
import Init.Data.List.Erase

/-!
# List Permutations

This file introduces the `List.Perm` relation, which is true if two lists are permutations of one
another.

## Notation

The notation `~` is used for permutation equivalence.
-/

open Nat

namespace List

open Perm (swap)

@[simp, refl] protected theorem Perm.refl : ∀ l : List α, l ~ l
  | [] => .nil
  | x :: xs => (Perm.refl xs).cons x

protected theorem Perm.rfl {l : List α} : l ~ l := .refl _

theorem Perm.of_eq (h : l₁ = l₂) : l₁ ~ l₂ := h ▸ .rfl

protected theorem Perm.symm {l₁ l₂ : List α} (h : l₁ ~ l₂) : l₂ ~ l₁ := by
  induction h with
  | nil => exact nil
  | cons _ _ ih => exact cons _ ih
  | swap => exact swap ..
  | trans _ _ ih₁ ih₂ => exact trans ih₂ ih₁

theorem perm_comm {l₁ l₂ : List α} : l₁ ~ l₂ ↔ l₂ ~ l₁ := ⟨Perm.symm, Perm.symm⟩

theorem Perm.swap' (x y : α) {l₁ l₂ : List α} (p : l₁ ~ l₂) : y :: x :: l₁ ~ x :: y :: l₂ :=
  (swap ..).trans <| p.cons _ |>.cons _

/--
Similar to `Perm.recOn`, but the `swap` case is generalized to `Perm.swap'`,
where the tail of the lists are not necessarily the same.
-/
@[elab_as_elim] theorem Perm.recOnSwap'
    {motive : (l₁ : List α) → (l₂ : List α) → l₁ ~ l₂ → Prop} {l₁ l₂ : List α} (p : l₁ ~ l₂)
    (nil : motive [] [] .nil)
    (cons : ∀ x {l₁ l₂}, (h : l₁ ~ l₂) → motive l₁ l₂ h → motive (x :: l₁) (x :: l₂) (.cons x h))
    (swap' : ∀ x y {l₁ l₂}, (h : l₁ ~ l₂) → motive l₁ l₂ h →
      motive (y :: x :: l₁) (x :: y :: l₂) (.swap' _ _ h))
    (trans : ∀ {l₁ l₂ l₃}, (h₁ : l₁ ~ l₂) → (h₂ : l₂ ~ l₃) → motive l₁ l₂ h₁ → motive l₂ l₃ h₂ →
      motive l₁ l₃ (.trans h₁ h₂)) : motive l₁ l₂ p :=
  have motive_refl l : motive l l (.refl l) :=
    List.recOn l nil fun x xs ih => cons x (.refl xs) ih
  Perm.recOn p nil cons (fun x y l => swap' x y (.refl l) (motive_refl l)) trans

theorem Perm.eqv (α) : Equivalence (@Perm α) := ⟨.refl, .symm, .trans⟩

instance isSetoid (α) : Setoid (List α) := .mk Perm (Perm.eqv α)

theorem Perm.mem_iff {a : α} {l₁ l₂ : List α} (p : l₁ ~ l₂) : a ∈ l₁ ↔ a ∈ l₂ := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp only [mem_cons, ih]
  | swap => simp only [mem_cons, or_left_comm]
  | trans _ _ ih₁ ih₂ => simp only [ih₁, ih₂]

theorem Perm.subset {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₁ ⊆ l₂ := fun _ => p.mem_iff.mp

theorem Perm.append_right {l₁ l₂ : List α} (t₁ : List α) (p : l₁ ~ l₂) : l₁ ++ t₁ ~ l₂ ++ t₁ := by
  induction p with
  | nil => rfl
  | cons _ _ ih => exact cons _ ih
  | swap => exact swap ..
  | trans _ _ ih₁ ih₂ => exact trans ih₁ ih₂

theorem Perm.append_left {t₁ t₂ : List α} : ∀ l : List α, t₁ ~ t₂ → l ++ t₁ ~ l ++ t₂
  | [], p => p
  | x :: xs, p => (p.append_left xs).cons x

theorem Perm.append {l₁ l₂ t₁ t₂ : List α} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) : l₁ ++ t₁ ~ l₂ ++ t₂ :=
  (p₁.append_right t₁).trans (p₂.append_left l₂)

theorem Perm.append_cons (a : α) {h₁ h₂ t₁ t₂ : List α} (p₁ : h₁ ~ h₂) (p₂ : t₁ ~ t₂) :
    h₁ ++ a :: t₁ ~ h₂ ++ a :: t₂ := p₁.append (p₂.cons a)

@[simp] theorem perm_middle {a : α} : ∀ {l₁ l₂ : List α}, l₁ ++ a :: l₂ ~ a :: (l₁ ++ l₂)
  | [], _ => .refl _
  | b :: _, _ => (Perm.cons _ perm_middle).trans (swap a b _)

@[simp] theorem perm_append_singleton (a : α) (l : List α) : l ++ [a] ~ a :: l :=
  perm_middle.trans <| by rw [append_nil]

theorem perm_append_comm : ∀ {l₁ l₂ : List α}, l₁ ++ l₂ ~ l₂ ++ l₁
  | [], _ => by simp
  | _ :: _, _ => (perm_append_comm.cons _).trans perm_middle.symm

theorem perm_append_comm_assoc (l₁ l₂ l₃ : List α) :
    Perm (l₁ ++ (l₂ ++ l₃)) (l₂ ++ (l₁ ++ l₃)) := by
  simpa only [List.append_assoc] using perm_append_comm.append_right _

theorem concat_perm (l : List α) (a : α) : concat l a ~ a :: l := by simp

theorem Perm.length_eq {l₁ l₂ : List α} (p : l₁ ~ l₂) : length l₁ = length l₂ := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp only [length_cons, ih]
  | swap => rfl
  | trans _ _ ih₁ ih₂ => simp only [ih₁, ih₂]

theorem Perm.contains_eq [BEq α] {l₁ l₂ : List α} (h : l₁ ~ l₂) {a : α} :
    l₁.contains a = l₂.contains a := by
  induction h with
  | nil => rfl
  | cons => simp_all
  | swap => simp only [contains_cons, ← Bool.or_assoc, Bool.or_comm]
  | trans => simp_all

theorem Perm.eq_nil {l : List α} (p : l ~ []) : l = [] := eq_nil_of_length_eq_zero p.length_eq

theorem Perm.nil_eq {l : List α} (p : [] ~ l) : [] = l := p.symm.eq_nil.symm

@[simp] theorem perm_nil {l₁ : List α} : l₁ ~ [] ↔ l₁ = [] :=
  ⟨fun p => p.eq_nil, fun e => e ▸ .rfl⟩

@[simp] theorem nil_perm {l₁ : List α} : [] ~ l₁ ↔ l₁ = [] := perm_comm.trans perm_nil

theorem not_perm_nil_cons (x : α) (l : List α) : ¬[] ~ x :: l := (nomatch ·.symm.eq_nil)

theorem not_perm_cons_nil {l : List α} {a : α} : ¬(Perm (a::l) []) :=
  fun h => by simpa using h.length_eq

theorem Perm.isEmpty_eq {l l' : List α} (h : Perm l l') : l.isEmpty = l'.isEmpty := by
  cases l <;> cases l' <;> simp_all

@[simp] theorem reverse_perm : ∀ l : List α, reverse l ~ l
  | [] => .nil
  | a :: l => reverse_cons .. ▸ (perm_append_singleton _ _).trans ((reverse_perm l).cons a)

theorem perm_cons_append_cons {l l₁ l₂ : List α} (a : α) (p : l ~ l₁ ++ l₂) :
    a :: l ~ l₁ ++ a :: l₂ := (p.cons a).trans perm_middle.symm

@[simp] theorem perm_replicate {n : Nat} {a : α} {l : List α} :
    l ~ replicate n a ↔ l = replicate n a := by
  refine ⟨fun p => eq_replicate_iff.2 ?_, fun h => h ▸ .rfl⟩
  exact ⟨p.length_eq.trans <| length_replicate .., fun _b m => eq_of_mem_replicate <| p.subset m⟩

@[simp] theorem replicate_perm {n : Nat} {a : α} {l : List α} :
    replicate n a ~ l ↔ replicate n a = l := (perm_comm.trans perm_replicate).trans eq_comm

@[simp] theorem perm_singleton {a : α} {l : List α} : l ~ [a] ↔ l = [a] := perm_replicate (n := 1)

@[simp] theorem singleton_perm {a : α} {l : List α} : [a] ~ l ↔ [a] = l := replicate_perm (n := 1)

theorem Perm.eq_singleton (h : l ~ [a]) : l = [a] := perm_singleton.mp h
theorem Perm.singleton_eq (h : [a] ~ l) : [a] = l := singleton_perm.mp h

theorem singleton_perm_singleton {a b : α} : [a] ~ [b] ↔ a = b := by simp

theorem perm_cons_erase [DecidableEq α] {a : α} {l : List α} (h : a ∈ l) : l ~ a :: l.erase a :=
  let ⟨_l₁, _l₂, _, e₁, e₂⟩ := exists_erase_eq h
  e₂ ▸ e₁ ▸ perm_middle

theorem Perm.filterMap (f : α → Option β) {l₁ l₂ : List α} (p : l₁ ~ l₂) :
    filterMap f l₁ ~ filterMap f l₂ := by
  induction p with
  | nil => simp
  | cons x _p IH => cases h : f x <;> simp [h, filterMap_cons, IH, Perm.cons]
  | swap x y l₂ => cases hx : f x <;> cases hy : f y <;> simp [hx, hy, filterMap_cons, swap]
  | trans _p₁ _p₂ IH₁ IH₂ => exact IH₁.trans IH₂

theorem Perm.map (f : α → β) {l₁ l₂ : List α} (p : l₁ ~ l₂) : map f l₁ ~ map f l₂ :=
  filterMap_eq_map f ▸ p.filterMap _

theorem Perm.pmap {p : α → Prop} (f : ∀ a, p a → β) {l₁ l₂ : List α} (p : l₁ ~ l₂) {H₁ H₂} :
    pmap f l₁ H₁ ~ pmap f l₂ H₂ := by
  induction p with
  | nil => simp
  | cons x _p IH => simp [IH, Perm.cons]
  | swap x y => simp [swap]
  | trans _p₁ p₂ IH₁ IH₂ => exact IH₁.trans (IH₂ (H₁ := fun a m => H₂ a (p₂.subset m)))

theorem Perm.filter (p : α → Bool) {l₁ l₂ : List α} (s : l₁ ~ l₂) :
    filter p l₁ ~ filter p l₂ := by rw [← filterMap_eq_filter]; apply s.filterMap

theorem filter_append_perm (p : α → Bool) (l : List α) :
    filter p l ++ filter (fun x => !p x) l ~ l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases h : p x <;> simp [h]
    · exact ih.cons x
    · exact Perm.trans (perm_append_comm.trans (perm_append_comm.cons _)) (ih.cons x)

theorem exists_perm_sublist {l₁ l₂ l₂' : List α} (s : l₁ <+ l₂) (p : l₂ ~ l₂') :
    ∃ l₁', l₁' ~ l₁ ∧ l₁' <+ l₂' := by
  induction p generalizing l₁ with
  | nil => exact ⟨[], sublist_nil.mp s ▸ .rfl, nil_sublist _⟩
  | cons x _ IH =>
    match s with
    | .cons _ s => let ⟨l₁', p', s'⟩ := IH s; exact ⟨l₁', p', s'.cons _⟩
    | .cons₂ _ s => let ⟨l₁', p', s'⟩ := IH s; exact ⟨x :: l₁', p'.cons x, s'.cons₂ _⟩
  | swap x y l' =>
    match s with
    | .cons _ (.cons _ s) => exact ⟨_, .rfl, (s.cons _).cons _⟩
    | .cons _ (.cons₂ _ s) => exact ⟨x :: _, .rfl, (s.cons _).cons₂ _⟩
    | .cons₂ _ (.cons _ s) => exact ⟨y :: _, .rfl, (s.cons₂ _).cons _⟩
    | .cons₂ _ (.cons₂ _ s) => exact ⟨x :: y :: _, .swap .., (s.cons₂ _).cons₂ _⟩
  | trans _ _ IH₁ IH₂ =>
    let ⟨m₁, pm, sm⟩ := IH₁ s
    let ⟨r₁, pr, sr⟩ := IH₂ sm
    exact ⟨r₁, pr.trans pm, sr⟩

theorem Perm.sizeOf_eq_sizeOf [SizeOf α] {l₁ l₂ : List α} (h : l₁ ~ l₂) :
    sizeOf l₁ = sizeOf l₂ := by
  induction h with
  | nil => rfl
  | cons _ _ h_sz₁₂ => simp [h_sz₁₂]
  | swap => simp [Nat.add_left_comm]
  | trans _ _ h_sz₁₂ h_sz₂₃ => simp [h_sz₁₂, h_sz₂₃]

theorem Sublist.exists_perm_append {l₁ l₂ : List α} : l₁ <+ l₂ → ∃ l, l₂ ~ l₁ ++ l
  | Sublist.slnil => ⟨nil, .rfl⟩
  | Sublist.cons a s =>
    let ⟨l, p⟩ := Sublist.exists_perm_append s
    ⟨a :: l, (p.cons a).trans perm_middle.symm⟩
  | Sublist.cons₂ a s =>
    let ⟨l, p⟩ := Sublist.exists_perm_append s
    ⟨l, p.cons a⟩

theorem Perm.countP_eq (p : α → Bool) {l₁ l₂ : List α} (s : l₁ ~ l₂) :
    countP p l₁ = countP p l₂ := by
  simp only [countP_eq_length_filter]
  exact (s.filter _).length_eq

theorem Perm.countP_congr {l₁ l₂ : List α} (s : l₁ ~ l₂) {p p' : α → Bool}
    (hp : ∀ x ∈ l₁, p x = p' x) : l₁.countP p = l₂.countP p' := by
  rw [← s.countP_eq p']
  clear s
  induction l₁ with
  | nil => rfl
  | cons y s hs =>
    simp only [mem_cons, forall_eq_or_imp] at hp
    simp only [countP_cons, hs hp.2, hp.1]

theorem countP_eq_countP_filter_add (l : List α) (p q : α → Bool) :
    l.countP p = (l.filter q).countP p + (l.filter fun a => !q a).countP p :=
  countP_append .. ▸ Perm.countP_eq _ (filter_append_perm _ _).symm

theorem Perm.count_eq [DecidableEq α] {l₁ l₂ : List α} (p : l₁ ~ l₂) (a) :
    count a l₁ = count a l₂ := p.countP_eq _

/-
This theorem is a variant of `Perm.foldl_eq` defined in Mathlib which uses typeclasses rather
than the explicit `comm` argument.
-/
theorem Perm.foldl_eq' {f : β → α → β} {l₁ l₂ : List α} (p : l₁ ~ l₂)
    (comm : ∀ x ∈ l₁, ∀ y ∈ l₁, ∀ (z), f (f z x) y = f (f z y) x)
    (init) : foldl f init l₁ = foldl f init l₂ := by
  induction p using recOnSwap' generalizing init with
  | nil => simp
  | cons x _p IH =>
    simp only [foldl]
    apply IH; intros; apply comm <;> exact .tail _ ‹_›
  | swap' x y _p IH =>
    simp only [foldl]
    rw [comm x (.tail _ <| .head _) y (.head _)]
    apply IH; intros; apply comm <;> exact .tail _ (.tail _ ‹_›)
  | trans p₁ _p₂ IH₁ IH₂ =>
    refine (IH₁ comm init).trans (IH₂ ?_ _)
    intros; apply comm <;> apply p₁.symm.subset <;> assumption

/-
This theorem is a variant of `Perm.foldr_eq` defined in Mathlib which uses typeclasses rather
than the explicit `comm` argument.
-/
theorem Perm.foldr_eq' {f : α → β → β} {l₁ l₂ : List α} (p : l₁ ~ l₂)
    (comm : ∀ x ∈ l₁, ∀ y ∈ l₁, ∀ (z), f y (f x z) = f x (f y z))
    (init) : foldr f init l₁ = foldr f init l₂ := by
  induction p using recOnSwap' generalizing init with
  | nil => simp
  | cons x _p IH =>
    simp only [foldr]
    congr 1
    apply IH; intros; apply comm <;> exact .tail _ ‹_›
  | swap' x y _p IH =>
    simp only [foldr]
    rw [comm x (.tail _ <| .head _) y (.head _)]
    congr 2
    apply IH; intros; apply comm <;> exact .tail _ (.tail _ ‹_›)
  | trans p₁ _p₂ IH₁ IH₂ =>
    refine (IH₁ comm init).trans (IH₂ ?_ _)
    intros; apply comm <;> apply p₁.symm.subset <;> assumption

theorem Perm.rec_heq {β : List α → Sort _} {f : ∀ a l, β l → β (a :: l)} {b : β []} {l l' : List α}
    (hl : l ~ l') (f_congr : ∀ {a l l' b b'}, l ~ l' → HEq b b' → HEq (f a l b) (f a l' b'))
    (f_swap : ∀ {a a' l b}, HEq (f a (a' :: l) (f a' l b)) (f a' (a :: l) (f a l b))) :
    HEq (@List.rec α β b f l) (@List.rec α β b f l') := by
  induction hl with
  | nil => rfl
  | cons a h ih => exact f_congr h ih
  | swap a a' l => exact f_swap
  | trans _h₁ _h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Lemma used to destruct perms element by element. -/
theorem perm_inv_core {a : α} {l₁ l₂ r₁ r₂ : List α} :
    l₁ ++ a :: r₁ ~ l₂ ++ a :: r₂ → l₁ ++ r₁ ~ l₂ ++ r₂ := by
  -- Necessary generalization for `induction`
  suffices ∀ s₁ s₂ (_ : s₁ ~ s₂) {l₁ l₂ r₁ r₂},
      l₁ ++ a :: r₁ = s₁ → l₂ ++ a :: r₂ = s₂ → l₁ ++ r₁ ~ l₂ ++ r₂ from (this _ _ · rfl rfl)
  intro s₁ s₂ p
  induction p using Perm.recOnSwap' with intro l₁ l₂ r₁ r₂ e₁ e₂
  | nil =>
    simp at e₁
  | cons x p IH =>
    cases l₁ <;> cases l₂ <;>
      dsimp at e₁ e₂ <;> injections <;> subst_vars
    · exact p
    · exact p.trans perm_middle
    · exact perm_middle.symm.trans p
    · exact (IH rfl rfl).cons _
  | swap' x y p IH =>
    obtain _ | ⟨y, _ | ⟨z, l₁⟩⟩ := l₁
      <;> obtain _ | ⟨u, _ | ⟨v, l₂⟩⟩ := l₂
      <;> dsimp at e₁ e₂ <;> injections <;> subst_vars
      <;> try exact p.cons _
    · exact (p.trans perm_middle).cons u
    · exact ((p.trans perm_middle).cons _).trans (swap _ _ _)
    · exact (perm_middle.symm.trans p).cons y
    · exact (swap _ _ _).trans ((perm_middle.symm.trans p).cons u)
    · exact (IH rfl rfl).swap' _ _
  | trans p₁ p₂ IH₁ IH₂ =>
    subst e₁ e₂
    obtain ⟨l₂, r₂, rfl⟩ := append_of_mem (a := a) (p₁.subset (by simp))
    exact (IH₁ rfl rfl).trans (IH₂ rfl rfl)

theorem Perm.cons_inv {a : α} {l₁ l₂ : List α} : a :: l₁ ~ a :: l₂ → l₁ ~ l₂ :=
  perm_inv_core (l₁ := []) (l₂ := [])

@[simp] theorem perm_cons (a : α) {l₁ l₂ : List α} : a :: l₁ ~ a :: l₂ ↔ l₁ ~ l₂ :=
  ⟨.cons_inv, .cons a⟩

theorem perm_append_left_iff {l₁ l₂ : List α} : ∀ l, l ++ l₁ ~ l ++ l₂ ↔ l₁ ~ l₂
  | [] => .rfl
  | a :: l => (perm_cons a).trans (perm_append_left_iff l)

theorem perm_append_right_iff {l₁ l₂ : List α} (l) : l₁ ++ l ~ l₂ ++ l ↔ l₁ ~ l₂ := by
  refine ⟨fun p => ?_, .append_right _⟩
  exact (perm_append_left_iff _).1 <| perm_append_comm.trans <| p.trans perm_append_comm

section DecidableEq

variable [DecidableEq α]

theorem Perm.erase (a : α) {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₁.erase a ~ l₂.erase a :=
  if h₁ : a ∈ l₁ then
    have h₂ : a ∈ l₂ := p.subset h₁
    .cons_inv <| (perm_cons_erase h₁).symm.trans <| p.trans (perm_cons_erase h₂)
  else by
    have h₂ : a ∉ l₂ := mt p.mem_iff.2 h₁
    rw [erase_of_not_mem h₁, erase_of_not_mem h₂]; exact p

theorem cons_perm_iff_perm_erase {a : α} {l₁ l₂ : List α} :
    a :: l₁ ~ l₂ ↔ a ∈ l₂ ∧ l₁ ~ l₂.erase a := by
  refine ⟨fun h => ?_, fun ⟨m, h⟩ => (h.cons a).trans (perm_cons_erase m).symm⟩
  have : a ∈ l₂ := h.subset (mem_cons_self a l₁)
  exact ⟨this, (h.trans <| perm_cons_erase this).cons_inv⟩

theorem perm_iff_count {l₁ l₂ : List α} : l₁ ~ l₂ ↔ ∀ a, count a l₁ = count a l₂ := by
  refine ⟨Perm.count_eq, fun H => ?_⟩
  induction l₁ generalizing l₂ with
  | nil =>
    match l₂ with
    | nil => rfl
    | cons b l₂ =>
      specialize H b
      simp at H
  | cons a l₁ IH =>
    have : a ∈ l₂ := count_pos_iff.mp (by rw [← H]; simp)
    refine ((IH fun b => ?_).cons a).trans (perm_cons_erase this).symm
    specialize H b
    rw [(perm_cons_erase this).count_eq] at H
    by_cases h : b = a <;> simpa [h, count_cons, Nat.succ_inj'] using H

theorem isPerm_iff : ∀ {l₁ l₂ : List α}, l₁.isPerm l₂ ↔ l₁ ~ l₂
  | [], [] => by simp [isPerm, isEmpty]
  | [], _ :: _ => by simp [isPerm, isEmpty, Perm.nil_eq]
  | a :: l₁, l₂ => by simp [isPerm, isPerm_iff, cons_perm_iff_perm_erase]

instance decidablePerm (l₁ l₂ : List α) : Decidable (l₁ ~ l₂) := decidable_of_iff _ isPerm_iff

protected theorem Perm.insert (a : α) {l₁ l₂ : List α} (p : l₁ ~ l₂) :
    l₁.insert a ~ l₂.insert a := by
  if h : a ∈ l₁ then
    simp [h, p.subset h, p]
  else
    have := p.cons a
    simpa [h, mt p.mem_iff.2 h] using this

theorem perm_insert_swap (x y : α) (l : List α) :
    List.insert x (List.insert y l) ~ List.insert y (List.insert x l) := by
  by_cases xl : x ∈ l <;> by_cases yl : y ∈ l <;> simp [xl, yl]
  if xy : x = y then simp [xy] else
  simp [List.insert, xl, yl, xy, Ne.symm xy]
  constructor

end DecidableEq

theorem Perm.pairwise_iff {R : α → α → Prop} (S : ∀ {x y}, R x y → R y x) :
    ∀ {l₁ l₂ : List α} (_p : l₁ ~ l₂), Pairwise R l₁ ↔ Pairwise R l₂ :=
  suffices ∀ {l₁ l₂}, l₁ ~ l₂ → Pairwise R l₁ → Pairwise R l₂
    from fun p => ⟨this p, this p.symm⟩
  fun {l₁ l₂} p d => by
    induction d generalizing l₂ with
    | nil => rw [← p.nil_eq]; constructor
    | cons h _ IH =>
      have : _ ∈ l₂ := p.subset (mem_cons_self _ _)
      obtain ⟨s₂, t₂, rfl⟩ := append_of_mem this
      have p' := (p.trans perm_middle).cons_inv
      refine (pairwise_middle S).2 (pairwise_cons.2 ⟨fun b m => ?_, IH p'⟩)
      exact h _ (p'.symm.subset m)

theorem Pairwise.perm {R : α → α → Prop} {l l' : List α} (hR : l.Pairwise R) (hl : l ~ l')
    (hsymm : ∀ {x y}, R x y → R y x) : l'.Pairwise R := (hl.pairwise_iff hsymm).mp hR

theorem Perm.pairwise {R : α → α → Prop} {l l' : List α} (hl : l ~ l') (hR : l.Pairwise R)
    (hsymm : ∀ {x y}, R x y → R y x) : l'.Pairwise R := hR.perm hl hsymm

/--
If two lists are sorted by an antisymmetric relation, and permutations of each other,
they must be equal.
-/
theorem Perm.eq_of_sorted : ∀ {l₁ l₂ : List α}
    (_ : ∀ a b, a ∈ l₁ → b ∈ l₂ → le a b → le b a → a = b)
    (_ : l₁.Pairwise le) (_ : l₂.Pairwise le) (_ : l₁ ~ l₂), l₁ = l₂
  | [], [], _, _, _, _ => rfl
  | [], b :: l₂, _, _, _, h => by simp_all
  | a :: l₁, [], _, _, _, h => by simp_all
  | a :: l₁, b :: l₂, w, h₁, h₂, h => by
    have am : a ∈ b :: l₂ := h.subset (mem_cons_self _ _)
    have bm : b ∈ a :: l₁ := h.symm.subset (mem_cons_self _ _)
    have ab : a = b := by
      simp only [mem_cons] at am
      rcases am with rfl | am
      · rfl
      · simp only [mem_cons] at bm
        rcases bm with rfl | bm
        · rfl
        · exact w _ _ (mem_cons_self _ _) (mem_cons_self _ _)
            (rel_of_pairwise_cons h₁ bm) (rel_of_pairwise_cons h₂ am)
    subst ab
    simp only [perm_cons] at h
    have := Perm.eq_of_sorted
      (fun x y hx hy => w x y (mem_cons_of_mem a hx) (mem_cons_of_mem a hy))
      h₁.tail h₂.tail h
    simp_all

theorem Nodup.perm {l l' : List α} (hR : l.Nodup) (hl : l ~ l') : l'.Nodup :=
  Pairwise.perm hR hl (by intro x y h h'; simp_all)

theorem Perm.nodup {l l' : List α} (hl : l ~ l') (hR : l.Nodup) : l'.Nodup := hR.perm hl

theorem Perm.nodup_iff {l₁ l₂ : List α} : l₁ ~ l₂ → (Nodup l₁ ↔ Nodup l₂) :=
  Perm.pairwise_iff <| @Ne.symm α

theorem Perm.flatten {l₁ l₂ : List (List α)} (h : l₁ ~ l₂) : l₁.flatten ~ l₂.flatten := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [flatten_cons, perm_append_left_iff, ih]
  | swap => simp only [flatten_cons, ← append_assoc, perm_append_right_iff]; exact perm_append_comm ..
  | trans _ _ ih₁ ih₂ => exact trans ih₁ ih₂

@[deprecated Perm.flatten (since := "2024-10-14")] abbrev Perm.join := @Perm.flatten

theorem Perm.flatMap_right {l₁ l₂ : List α} (f : α → List β) (p : l₁ ~ l₂) : l₁.flatMap f ~ l₂.flatMap f :=
  (p.map _).flatten

@[deprecated Perm.flatMap_right (since := "2024-10-16")] abbrev Perm.bind_right := @Perm.flatMap_right

theorem Perm.eraseP (f : α → Bool) {l₁ l₂ : List α}
    (H : Pairwise (fun a b => f a → f b → False) l₁) (p : l₁ ~ l₂) : eraseP f l₁ ~ eraseP f l₂ := by
  induction p with
  | nil => simp
  | cons a p IH =>
    if h : f a then simp [h, p]
    else simp [h]; exact IH (pairwise_cons.1 H).2
  | swap a b l =>
    by_cases h₁ : f a <;> by_cases h₂ : f b <;> simp [h₁, h₂]
    · cases (pairwise_cons.1 H).1 _ (mem_cons.2 (Or.inl rfl)) h₂ h₁
    · apply swap
  | trans p₁ _ IH₁ IH₂ =>
    refine (IH₁ H).trans (IH₂ ((p₁.pairwise_iff ?_).1 H))
    exact fun h h₁ h₂ => h h₂ h₁

end List
