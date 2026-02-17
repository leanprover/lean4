/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

prelude
public import Init.Data.List.Attach
import Init.ByCases
import Init.Data.List.Count
import Init.Data.List.Sublist
import Init.Data.List.TakeDrop
import Init.Data.Option.Lemmas

public section

/-!
# Lemmas about `List.Pairwise` and `List.Nodup`.
-/

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

open Nat

/-! ## Pairwise and Nodup -/

/-! ### Pairwise -/

theorem pairwise_iff_getElem {l : List α} : Pairwise R l ↔
    ∀ (i j : Nat) (_hi : i < l.length) (_hj : j < l.length) (_hij : i < j), R l[i] l[j] := by
  induction l with | nil => simp | cons a l ihl =>
    simp only [pairwise_cons, length_cons, mem_iff_getElem, ihl,
        forall_exists_index, Nat.lt_succ_iff]
    exact ⟨ fun h =>
              fun | 0, _ + 1, _, _, _ => h.1 _ _ _ rfl
                  | _ + 1, _ + 1, _, _, hij => h.2 _ _ _ _ <| lt_of_succ_lt_succ hij,
            fun h =>
          ⟨   fun | _, _, hj, Eq.refl _ => h _ _ (Nat.zero_le _) hj <| Nat.zero_lt_succ _,
              fun _ _ hi hj hij => h (_ + 1) (_ + 1) hi hj <| Nat.succ_lt_succ hij⟩⟩

theorem Pairwise.rel_getElem_of_lt {l : List α} {i j} {hi : i < l.length} {hj : j < l.length}
    (h : Pairwise R l) : i < j → R l[i] l[j] := pairwise_iff_getElem.mp h _ _ _ _

@[grind →] theorem Pairwise.sublist : l₁ <+ l₂ → l₂.Pairwise R → l₁.Pairwise R
  | .slnil, h => h
  | .cons _ s, .cons _ h₂ => h₂.sublist s
  | .cons₂ _ s, .cons h₁ h₂ => (h₂.sublist s).cons fun _ h => h₁ _ (s.subset h)

theorem Pairwise.imp {α R S} (H : ∀ {a b}, R a b → S a b) :
    ∀ {l : List α}, l.Pairwise R → l.Pairwise S
  | _, .nil => .nil
  | _, .cons h₁ h₂ => .cons (H ∘ h₁ ·) (h₂.imp H)

theorem rel_of_pairwise_cons (p : (a :: l).Pairwise R) : ∀ {a'}, a' ∈ l → R a a' :=
  (pairwise_cons.1 p).1 _

@[grind →] theorem Pairwise.of_cons (p : (a :: l).Pairwise R) : Pairwise R l :=
  (pairwise_cons.1 p).2

set_option linter.unusedVariables false in
@[grind ←] theorem Pairwise.tail : ∀ {l : List α} (h : Pairwise R l), Pairwise R l.tail
  | [], h => h
  | _ :: _, h => h.of_cons

theorem Pairwise.imp_of_mem {S : α → α → Prop}
    (H : ∀ {a b}, a ∈ l → b ∈ l → R a b → S a b) (p : Pairwise R l) : Pairwise S l := by
  induction p with
  | nil => constructor
  | @cons a l r _ ih =>
    constructor
    · exact fun x h => H (mem_cons_self ..) (mem_cons_of_mem _ h) <| r x h
    · exact ih fun m m' => H (mem_cons_of_mem _ m) (mem_cons_of_mem _ m')

theorem Pairwise.and (hR : Pairwise R l) (hS : Pairwise S l) :
    l.Pairwise fun a b => R a b ∧ S a b := by
  rw [pairwise_iff_getElem] at hR hS ⊢
  simp only [imp_and, forall_and]
  exact ⟨hR, hS⟩

theorem pairwise_and_iff : l.Pairwise (fun a b => R a b ∧ S a b) ↔ Pairwise R l ∧ Pairwise S l :=
  ⟨fun h => ⟨h.imp fun h => h.1, h.imp fun h => h.2⟩, fun ⟨hR, hS⟩ => hR.and hS⟩

theorem Pairwise.imp₂ (H : ∀ a b, R a b → S a b → T a b)
    (hR : Pairwise R l) (hS : l.Pairwise S) : l.Pairwise T :=
  (hR.and hS).imp fun ⟨h₁, h₂⟩ => H _ _ h₁ h₂

theorem Pairwise.iff_of_mem {S : α → α → Prop} {l : List α}
    (H : ∀ {a b}, a ∈ l → b ∈ l → (R a b ↔ S a b)) : Pairwise R l ↔ Pairwise S l :=
  ⟨Pairwise.imp_of_mem fun m m' => (H m m').1, Pairwise.imp_of_mem fun m m' => (H m m').2⟩

theorem Pairwise.iff {S : α → α → Prop} (H : ∀ a b, R a b ↔ S a b) {l : List α} :
    Pairwise R l ↔ Pairwise S l :=
  Pairwise.iff_of_mem fun _ _ => H ..

theorem pairwise_of_forall {l : List α} (H : ∀ x y, R x y) : Pairwise R l := by
  induction l <;> simp [*]

theorem Pairwise.and_mem {l : List α} :
    Pairwise R l ↔ Pairwise (fun x y => x ∈ l ∧ y ∈ l ∧ R x y) l :=
  Pairwise.iff_of_mem <| by simp +contextual

theorem Pairwise.imp_mem {l : List α} :
    Pairwise R l ↔ Pairwise (fun x y => x ∈ l → y ∈ l → R x y) l :=
  Pairwise.iff_of_mem <| by simp +contextual

theorem Pairwise.forall_of_forall_of_flip (h₁ : ∀ x ∈ l, R x x) (h₂ : Pairwise R l)
    (h₃ : l.Pairwise (flip R)) : ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → R x y := by
  induction l with
  | nil => exact forall_mem_nil _
  | cons a l ih =>
    rw [pairwise_cons] at h₂ h₃
    simp only [mem_cons]
    rintro x (rfl | hx) y (rfl | hy)
    · exact h₁ _ l.mem_cons_self
    · exact h₂.1 _ hy
    · exact h₃.1 _ hx
    · exact ih (fun x hx => h₁ _ <| mem_cons_of_mem _ hx) h₂.2 h₃.2 hx hy

@[grind ←] theorem pairwise_singleton (R) (a : α) : Pairwise R [a] := by simp

@[grind =] theorem pairwise_pair {a b : α} : Pairwise R [a, b] ↔ R a b := by simp

@[grind =] theorem pairwise_map {l : List α} :
    (l.map f).Pairwise R ↔ l.Pairwise fun a b => R (f a) (f b) := by
  induction l
  · simp
  · simp only [map, pairwise_cons, forall_mem_map, *]

theorem Pairwise.of_map {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, S (f a) (f b) → R a b)
    (p : Pairwise S (map f l)) : Pairwise R l :=
  (pairwise_map.1 p).imp (H _ _)

@[grind <=] theorem Pairwise.map {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, R a b → S (f a) (f b))
    (p : Pairwise R l) : Pairwise S (map f l) :=
  pairwise_map.2 <| p.imp (H _ _)

@[grind =] theorem pairwise_filterMap {f : β → Option α} {l : List β} :
    Pairwise R (filterMap f l) ↔ Pairwise (fun a a' : β => ∀ b, f a = some b → ∀ b', f a' = some b' → R b b') l := by
  let _S (a a' : β) := ∀ b, f a = some b → ∀ b', f a' = some b' → R b b'
  induction l with
  | nil => simp only [filterMap, Pairwise.nil]
  | cons a l IH => ?_
  match e : f a with
  | none =>
    rw [filterMap_cons_none e, pairwise_cons]
    simp only [e, false_implies, implies_true, true_and, IH, reduceCtorEq]
  | some b =>
    rw [filterMap_cons_some e]
    simpa [IH, e] using fun _ =>
      ⟨fun h a ha b hab => h _ _ ha hab, fun h a b ha hab => h _ ha _ hab⟩

@[grind <=] theorem Pairwise.filterMap {S : β → β → Prop} (f : α → Option β)
    (H : ∀ a a' : α, R a a' → ∀ b, f a = some b → ∀ b', f a' = some b' → S b b') {l : List α} (p : Pairwise R l) :
    Pairwise S (filterMap f l) :=
  pairwise_filterMap.2 <| p.imp (H _ _)

@[grind =] theorem pairwise_filter {p : α → Bool} {l : List α} :
    Pairwise R (filter p l) ↔ Pairwise (fun x y => p x → p y → R x y) l := by
  rw [← filterMap_eq_filter, pairwise_filterMap]
  simp

@[grind ←] theorem Pairwise.filter (p : α → Bool) : Pairwise R l → Pairwise R (filter p l) :=
  Pairwise.sublist filter_sublist

@[grind =] theorem pairwise_append {l₁ l₂ : List α} :
    (l₁ ++ l₂).Pairwise R ↔ l₁.Pairwise R ∧ l₂.Pairwise R ∧ ∀ a ∈ l₁, ∀ b ∈ l₂, R a b := by
  induction l₁ <;> simp [*, or_imp, forall_and, and_assoc, and_left_comm]

theorem pairwise_append_comm {R : α → α → Prop} (s : ∀ {x y}, R x y → R y x) {l₁ l₂ : List α} :
    Pairwise R (l₁ ++ l₂) ↔ Pairwise R (l₂ ++ l₁) := by
  have (l₁ l₂ : List α) (H : ∀ x : α, x ∈ l₁ → ∀ y : α, y ∈ l₂ → R x y)
    (x : α) (xm : x ∈ l₂) (y : α) (ym : y ∈ l₁) : R x y := s (H y ym x xm)
  simp only [pairwise_append, and_left_comm]; rw [Iff.intro (this l₁ l₂) (this l₂ l₁)]

@[grind =] theorem pairwise_middle {R : α → α → Prop} (s : ∀ {x y}, R x y → R y x) {a : α} {l₁ l₂ : List α} :
    Pairwise R (l₁ ++ a :: l₂) ↔ Pairwise R (a :: (l₁ ++ l₂)) := by
  change Pairwise R (l₁ ++ ([a] ++ l₂)) ↔ Pairwise R ([a] ++ l₁ ++ l₂)
  rw [← append_assoc, pairwise_append, @pairwise_append _ _ ([a] ++ l₁), pairwise_append_comm s]
  simp only [mem_append, or_comm]

@[grind =] theorem pairwise_flatten {L : List (List α)} :
    Pairwise R (flatten L) ↔
      (∀ l ∈ L, Pairwise R l) ∧ Pairwise (fun l₁ l₂ => ∀ x ∈ l₁, ∀ y ∈ l₂, R x y) L := by
  induction L with
  | nil => simp
  | cons l L IH =>
    simp only [flatten_cons, pairwise_append, IH, mem_flatten, exists_imp, and_imp, forall_mem_cons,
      pairwise_cons, and_assoc, and_congr_right_iff]
    rw [and_comm, and_congr_left_iff]
    intros; exact ⟨fun h l' b c d e => h c d e l' b, fun h c d e l' b => h l' b c d e⟩

@[grind =] theorem pairwise_flatMap {R : β → β → Prop} {l : List α} {f : α → List β} :
    List.Pairwise R (l.flatMap f) ↔
      (∀ a ∈ l, Pairwise R (f a)) ∧ Pairwise (fun a₁ a₂ => ∀ x ∈ f a₁, ∀ y ∈ f a₂, R x y) l := by
  simp [List.flatMap, pairwise_flatten, pairwise_map]

@[grind =] theorem pairwise_reverse {l : List α} :
    l.reverse.Pairwise R ↔ l.Pairwise (fun a b => R b a) := by
  induction l <;> simp [*, pairwise_append, and_comm]

@[simp, grind =] theorem pairwise_replicate {n : Nat} {a : α} :
    (replicate n a).Pairwise R ↔ n ≤ 1 ∨ R a a := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [replicate_succ, pairwise_cons, mem_replicate, ne_eq, and_imp,
      forall_eq_apply_imp_iff, ih]
    constructor
    · rintro ⟨h, h' | h'⟩
      · by_cases w : n = 0
        · left
          subst w
          simp
        · right
          exact h w
      · right
        exact h'
    · rintro (h | h)
      · obtain rfl := eq_zero_of_le_zero (le_of_lt_succ h)
        simp
      · exact ⟨fun _ => h, Or.inr h⟩

@[grind ←] theorem Pairwise.drop {l : List α} {i : Nat} (h : List.Pairwise R l) : List.Pairwise R (l.drop i) :=
  h.sublist (drop_sublist _ _)

@[grind ←] theorem Pairwise.take {l : List α} {i : Nat} (h : List.Pairwise R l) : List.Pairwise R (l.take i) :=
  h.sublist (take_sublist _ _)

-- This theorem is not annotated with `grind` because it leads to a loop of instantiations with `Pairwise.sublist`.
theorem pairwise_iff_forall_sublist : l.Pairwise R ↔ (∀ {a b}, [a,b] <+ l → R a b) := by
  induction l with
  | nil => simp
  | cons hd tl IH =>
    rw [List.pairwise_cons]
    constructor <;> intro h
    · intro
      | a, b, .cons _ hab => exact IH.mp h.2 hab
      | _, b, .cons₂ _ hab => refine h.1 _ (hab.subset ?_); simp
    · constructor
      · intro x hx
        apply h
        rw [List.cons_sublist_cons, List.singleton_sublist]
        exact hx
      · apply IH.mpr
        intro a b hab
        apply h; exact hab.cons _

theorem pairwise_of_forall_sublist (g : ∀ {a b}, [a,b] <+ l → R a b) : l.Pairwise R := pairwise_iff_forall_sublist.mpr g

theorem Pairwise.forall_sublist (h : l.Pairwise R) : ∀ {a b}, [a,b] <+ l → R a b := pairwise_iff_forall_sublist.mp h

theorem Pairwise.rel_of_mem_take_of_mem_drop
    {l : List α} (h : l.Pairwise R) (hx : x ∈ l.take i) (hy : y ∈ l.drop i) : R x y := by
  apply pairwise_iff_forall_sublist.mp h
  rw [← take_append_drop i l, sublist_append_iff]
  refine ⟨[x], [y], rfl, by simpa, by simpa⟩

theorem Pairwise.rel_of_mem_append
    {l₁ l₂ : List α} (h : (l₁ ++ l₂).Pairwise R) (hx : x ∈ l₁) (hy : y ∈ l₂) : R x y := by
  apply pairwise_iff_forall_sublist.mp h
  rw [sublist_append_iff]
  exact ⟨[x], [y], rfl, by simpa, by simpa⟩

theorem pairwise_of_forall_mem_list {l : List α} {r : α → α → Prop} (h : ∀ a ∈ l, ∀ b ∈ l, r a b) :
    l.Pairwise r := by
  rw [pairwise_iff_forall_sublist]
  intro a b hab
  apply h <;> (apply hab.subset; simp)

@[grind =] theorem pairwise_pmap {p : β → Prop} {f : ∀ b, p b → α} {l : List β} (h : ∀ x ∈ l, p x) :
    Pairwise R (l.pmap f h) ↔
      Pairwise (fun b₁ b₂ => ∀ (h₁ : p b₁) (h₂ : p b₂), R (f b₁ h₁) (f b₂ h₂)) l := by
  induction l with
  | nil => simp
  | cons a l ihl =>
    obtain ⟨_, hl⟩ : p a ∧ ∀ b, b ∈ l → p b := by simpa using h
    simp only [pmap_cons, pairwise_cons, mem_pmap, forall_exists_index, ihl hl, and_congr_left_iff]
    refine fun _ => ⟨fun H b hb _ hpb => H _ _ hb rfl, ?_⟩
    rintro H _ b hb rfl
    exact H b hb _ _

@[grind <=] theorem Pairwise.pmap {l : List α} (hl : Pairwise R l) {p : α → Prop} {f : ∀ a, p a → β}
    (h : ∀ x ∈ l, p x) {S : β → β → Prop}
    (hS : ∀ ⦃x⦄ (hx : p x) ⦃y⦄ (hy : p y), R x y → S (f x hx) (f y hy)) :
    Pairwise S (l.pmap f h) := by
  refine (pairwise_pmap h).2 (Pairwise.imp_of_mem ?_ hl)
  intros; apply hS; assumption

/-! ### Nodup -/

@[grind =] theorem nodup_iff_pairwise_ne : List.Nodup l ↔ List.Pairwise (· ≠ ·) l := Iff.rfl

theorem nodup_iff_eq_of_getElem_eq {l : List α} : List.Nodup l ↔
    ∀ (i j : Nat) (_hi : i < l.length) (_hj : j < l.length), l[i] = l[j] → i = j := by
  simp only [nodup_iff_pairwise_ne, pairwise_iff_getElem, Nat.le_antisymm_iff,
    ← Nat.not_le, Decidable.not_imp_not]
  exact ⟨fun h _ _ hi hj hij => ⟨h _ _ hj hi hij.symm, h _ _ hi hj hij⟩, (And.right <| · · · · · ·)⟩

theorem nodup_iff_getElem_inj {l : List α} : List.Nodup l ↔
    ∀ (i j : Nat) (_hi : i < l.length) (_hj : j < l.length), l[i] = l[j] ↔ i = j := by
  simp only [nodup_iff_eq_of_getElem_eq, iff_iff_implies_and_implies,
    forall_and, imp_self, true_and, and_imp]
  exact ⟨fun _ _ _ _ _ => (· ▸ rfl), flip <| fun _ => id⟩

theorem Nodup.getElem_eq_of_getElem_eq {xs : List α} (h : Nodup xs) {hi : i < xs.length}
    {hj : j < xs.length} : xs[i] = xs[j] → i = j := nodup_iff_eq_of_getElem_eq.mp h _ _ _ _

theorem Nodup.getElem_inj {xs : List α} (h : Nodup xs) {hi : i < xs.length}
    {hj : j < xs.length} : xs[i] = xs[j] ↔ i = j := nodup_iff_getElem_inj.mp h _ _ _ _

theorem Nodup.eq_of_getElem?_eq {xs : List α} (h : Nodup xs) (hi : i < xs.length)
    (hij : xs[i]? = xs[j]?) : i = j := by
  simp only [getElem?_pos xs i hi, some_eq_getElem?_iff, h.getElem_inj] at hij
  exact hij.choose_spec.symm

@[deprecated Nodup.eq_of_getElem?_eq (since := "2025-10-26")]
theorem getElem?_inj {xs : List α} (h₀ : i < xs.length) (h₁ : Nodup xs) (h₂ : xs[i]? = xs[j]?) :
    i = j := h₁.eq_of_getElem?_eq h₀ h₂

@[simp]
theorem nodup_nil : @Nodup α [] :=
  Pairwise.nil

grind_pattern nodup_nil => @Nodup α []

@[simp, grind =]
theorem nodup_cons {a : α} {l : List α} : Nodup (a :: l) ↔ a ∉ l ∧ Nodup l := by
  simp only [Nodup, pairwise_cons, forall_mem_ne]

@[grind =] theorem nodup_append {l₁ l₂ : List α} :
    (l₁ ++ l₂).Nodup ↔ l₁.Nodup ∧ l₂.Nodup ∧ ∀ a ∈ l₁, ∀ b ∈ l₂, a ≠ b :=
  pairwise_append

theorem Nodup.sublist : l₁ <+ l₂ → Nodup l₂ → Nodup l₁ :=
  Pairwise.sublist

grind_pattern Nodup.sublist => l₁ <+ l₂, Nodup l₁
grind_pattern Nodup.sublist => l₁ <+ l₂, Nodup l₂

theorem Sublist.nodup : l₁ <+ l₂ → Nodup l₂ → Nodup l₁ :=
  Nodup.sublist

@[simp, grind =] theorem nodup_replicate {n : Nat} {a : α} :
    (replicate n a).Nodup ↔ n ≤ 1 := by simp [Nodup]

theorem nodup_iff_count_of_mem [BEq α] [LawfulBEq α] {l : List α} :
    l.Nodup ↔ ∀ a ∈ l, count a l = 1 := by
  induction l with | nil => simp | cons b l ihl =>
  simp only [nodup_cons, mem_cons, forall_eq_or_imp, count_cons_self,
    succ_inj, count_eq_zero, and_congr_right_iff, ihl]
  exact fun hb => forall₂_congr fun a ha => count_cons_of_ne (hb <| · ▸ ha : b ≠ a) ▸ Iff.rfl

theorem nodup_iff_count_eq_ite [BEq α] [LawfulBEq α] {l : List α} :
    l.Nodup ↔ ∀ a, count a l = if a ∈ l then 1 else 0 := by
  rw [nodup_iff_count_of_mem]
  exact forall_congr' fun a => by if ha : a ∈ l then simp [ha] else simp [ha, count_eq_zero]

theorem Nodup.count [BEq α] [LawfulBEq α] {a : α} {l : List α} (h : Nodup l) :
    l.count a = if a ∈ l then 1 else 0 := nodup_iff_count_eq_ite.mp h _

theorem Nodup.count_of_mem [BEq α] [LawfulBEq α] {a : α} {l : List α} (h : Nodup l) (ha : a ∈ l) :
    l.count a = 1 := h.count ▸ if_pos ha

grind_pattern Nodup.count => count a l, Nodup l

@[grind =]
theorem nodup_iff_count [BEq α] [LawfulBEq α] {l : List α} : l.Nodup ↔ ∀ a, count a l ≤ 1 := by
  simp only [nodup_iff_count_of_mem, Nat.le_iff_lt_or_eq, Nat.lt_one_iff, count_eq_zero]
  exact forall_congr' fun _ => Decidable.imp_iff_not_or

end List
