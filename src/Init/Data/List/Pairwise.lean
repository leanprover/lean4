/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
prelude
import Init.Data.List.Sublist
import Init.Data.List.Attach

/-!
# Lemmas about `List.Pairwise` and `List.Nodup`.
-/

-- set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
-- set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

open Nat

/-! ## Pairwise and Nodup -/

/-! ### Pairwise -/

theorem Pairwise.sublist : l₁ <+ l₂ → l₂.Pairwise R → l₁.Pairwise R
  | .slnil, h => h
  | .cons _ s, .cons _ h₂ => h₂.sublist s
  | .cons₂ _ s, .cons h₁ h₂ => (h₂.sublist s).cons fun _ h => h₁ _ (s.subset h)

theorem Pairwise.imp {α R S} (H : ∀ {a b}, R a b → S a b) :
    ∀ {l : List α}, l.Pairwise R → l.Pairwise S
  | _, .nil => .nil
  | _, .cons h₁ h₂ => .cons (H ∘ h₁ ·) (h₂.imp H)

theorem rel_of_pairwise_cons (p : (a :: l).Pairwise R) : ∀ {a'}, a' ∈ l → R a a' :=
  (pairwise_cons.1 p).1 _

theorem Pairwise.of_cons (p : (a :: l).Pairwise R) : Pairwise R l :=
  (pairwise_cons.1 p).2

theorem Pairwise.tail : ∀ {l : List α} (_p : Pairwise R l), Pairwise R l.tail
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
  induction hR with
  | nil => simp only [Pairwise.nil]
  | cons R1 _ IH =>
    simp only [Pairwise.nil, pairwise_cons] at hS ⊢
    exact ⟨fun b bl => ⟨R1 b bl, hS.1 b bl⟩, IH hS.2⟩

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
    · exact h₁ _ (l.mem_cons_self _)
    · exact h₂.1 _ hy
    · exact h₃.1 _ hx
    · exact ih (fun x hx => h₁ _ <| mem_cons_of_mem _ hx) h₂.2 h₃.2 hx hy

theorem pairwise_singleton (R) (a : α) : Pairwise R [a] := by simp

theorem pairwise_pair {a b : α} : Pairwise R [a, b] ↔ R a b := by simp

theorem pairwise_map {l : List α} :
    (l.map f).Pairwise R ↔ l.Pairwise fun a b => R (f a) (f b) := by
  induction l
  · simp
  · simp only [map, pairwise_cons, forall_mem_map, *]

theorem Pairwise.of_map {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, S (f a) (f b) → R a b)
    (p : Pairwise S (map f l)) : Pairwise R l :=
  (pairwise_map.1 p).imp (H _ _)

theorem Pairwise.map {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, R a b → S (f a) (f b))
    (p : Pairwise R l) : Pairwise S (map f l) :=
  pairwise_map.2 <| p.imp (H _ _)

theorem pairwise_filterMap {f : β → Option α} {l : List β} :
    Pairwise R (filterMap f l) ↔ Pairwise (fun a a' : β => ∀ b ∈ f a, ∀ b' ∈ f a', R b b') l := by
  let _S (a a' : β) := ∀ b ∈ f a, ∀ b' ∈ f a', R b b'
  simp only [Option.mem_def]
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

theorem Pairwise.filterMap {S : β → β → Prop} (f : α → Option β)
    (H : ∀ a a' : α, R a a' → ∀ b ∈ f a, ∀ b' ∈ f a', S b b') {l : List α} (p : Pairwise R l) :
    Pairwise S (filterMap f l) :=
  pairwise_filterMap.2 <| p.imp (H _ _)

@[deprecated Pairwise.filterMap (since := "2024-07-29")] abbrev Pairwise.filter_map := @Pairwise.filterMap

theorem pairwise_filter {p : α → Prop} [DecidablePred p] {l : List α} :
    Pairwise R (filter p l) ↔ Pairwise (fun x y => p x → p y → R x y) l := by
  rw [← filterMap_eq_filter, pairwise_filterMap]
  simp

theorem Pairwise.filter (p : α → Bool) : Pairwise R l → Pairwise R (filter p l) :=
  Pairwise.sublist (filter_sublist _)

theorem pairwise_append {l₁ l₂ : List α} :
    (l₁ ++ l₂).Pairwise R ↔ l₁.Pairwise R ∧ l₂.Pairwise R ∧ ∀ a ∈ l₁, ∀ b ∈ l₂, R a b := by
  induction l₁ <;> simp [*, or_imp, forall_and, and_assoc, and_left_comm]

theorem pairwise_append_comm {R : α → α → Prop} (s : ∀ {x y}, R x y → R y x) {l₁ l₂ : List α} :
    Pairwise R (l₁ ++ l₂) ↔ Pairwise R (l₂ ++ l₁) := by
  have (l₁ l₂ : List α) (H : ∀ x : α, x ∈ l₁ → ∀ y : α, y ∈ l₂ → R x y)
    (x : α) (xm : x ∈ l₂) (y : α) (ym : y ∈ l₁) : R x y := s (H y ym x xm)
  simp only [pairwise_append, and_left_comm]; rw [Iff.intro (this l₁ l₂) (this l₂ l₁)]

theorem pairwise_middle {R : α → α → Prop} (s : ∀ {x y}, R x y → R y x) {a : α} {l₁ l₂ : List α} :
    Pairwise R (l₁ ++ a :: l₂) ↔ Pairwise R (a :: (l₁ ++ l₂)) := by
  show Pairwise R (l₁ ++ ([a] ++ l₂)) ↔ Pairwise R ([a] ++ l₁ ++ l₂)
  rw [← append_assoc, pairwise_append, @pairwise_append _ _ ([a] ++ l₁), pairwise_append_comm s]
  simp only [mem_append, or_comm]

theorem pairwise_flatten {L : List (List α)} :
    Pairwise R (flatten L) ↔
      (∀ l ∈ L, Pairwise R l) ∧ Pairwise (fun l₁ l₂ => ∀ x ∈ l₁, ∀ y ∈ l₂, R x y) L := by
  induction L with
  | nil => simp
  | cons l L IH =>
    simp only [flatten, pairwise_append, IH, mem_flatten, exists_imp, and_imp, forall_mem_cons,
      pairwise_cons, and_assoc, and_congr_right_iff]
    rw [and_comm, and_congr_left_iff]
    intros; exact ⟨fun h l' b c d e => h c d e l' b, fun h c d e l' b => h l' b c d e⟩

@[deprecated pairwise_flatten (since := "2024-10-14")] abbrev pairwise_join := @pairwise_flatten

theorem pairwise_flatMap {R : β → β → Prop} {l : List α} {f : α → List β} :
    List.Pairwise R (l.flatMap f) ↔
      (∀ a ∈ l, Pairwise R (f a)) ∧ Pairwise (fun a₁ a₂ => ∀ x ∈ f a₁, ∀ y ∈ f a₂, R x y) l := by
  simp [List.flatMap, pairwise_flatten, pairwise_map]

@[deprecated pairwise_flatMap (since := "2024-10-14")] abbrev pairwise_bind := @pairwise_flatMap

theorem pairwise_reverse {l : List α} :
    l.reverse.Pairwise R ↔ l.Pairwise (fun a b => R b a) := by
  induction l <;> simp [*, pairwise_append, and_comm]

@[simp] theorem pairwise_replicate {n : Nat} {a : α} :
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

theorem Pairwise.drop {l : List α} {i : Nat} (h : List.Pairwise R l) : List.Pairwise R (l.drop i) :=
  h.sublist (drop_sublist _ _)

theorem Pairwise.take {l : List α} {i : Nat} (h : List.Pairwise R l) : List.Pairwise R (l.take i) :=
  h.sublist (take_sublist _ _)

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

theorem pairwise_pmap {p : β → Prop} {f : ∀ b, p b → α} {l : List β} (h : ∀ x ∈ l, p x) :
    Pairwise R (l.pmap f h) ↔
      Pairwise (fun b₁ b₂ => ∀ (h₁ : p b₁) (h₂ : p b₂), R (f b₁ h₁) (f b₂ h₂)) l := by
  induction l with
  | nil => simp
  | cons a l ihl =>
    obtain ⟨_, hl⟩ : p a ∧ ∀ b, b ∈ l → p b := by simpa using h
    simp only [ihl hl, pairwise_cons, exists₂_imp, pmap, and_congr_left_iff, mem_pmap]
    refine fun _ => ⟨fun H b hb _ hpb => H _ _ hb rfl, ?_⟩
    rintro H _ b hb rfl
    exact H b hb _ _

theorem Pairwise.pmap {l : List α} (hl : Pairwise R l) {p : α → Prop} {f : ∀ a, p a → β}
    (h : ∀ x ∈ l, p x) {S : β → β → Prop}
    (hS : ∀ ⦃x⦄ (hx : p x) ⦃y⦄ (hy : p y), R x y → S (f x hx) (f y hy)) :
    Pairwise S (l.pmap f h) := by
  refine (pairwise_pmap h).2 (Pairwise.imp_of_mem ?_ hl)
  intros; apply hS; assumption

/-! ### Nodup -/

@[simp]
theorem nodup_nil : @Nodup α [] :=
  Pairwise.nil

@[simp]
theorem nodup_cons {a : α} {l : List α} : Nodup (a :: l) ↔ a ∉ l ∧ Nodup l := by
  simp only [Nodup, pairwise_cons, forall_mem_ne]

theorem Nodup.sublist : l₁ <+ l₂ → Nodup l₂ → Nodup l₁ :=
  Pairwise.sublist

theorem Sublist.nodup : l₁ <+ l₂ → Nodup l₂ → Nodup l₁ :=
  Nodup.sublist

theorem getElem?_inj {xs : List α}
    (h₀ : i < xs.length) (h₁ : Nodup xs) (h₂ : xs[i]? = xs[j]?) : i = j := by
  induction xs generalizing i j with
  | nil => cases h₀
  | cons x xs ih =>
    match i, j with
    | 0, 0 => rfl
    | i+1, j+1 =>
      cases h₁ with
      | cons ha h₁ =>
        simp only [getElem?_cons_succ] at h₂
        exact congrArg (· + 1) (ih (Nat.lt_of_succ_lt_succ h₀) h₁ h₂)
    | i+1, 0 => ?_
    | 0, j+1 => ?_
    all_goals
      simp only [get?_eq_getElem?, getElem?_cons_zero, getElem?_cons_succ] at h₂
      cases h₁; rename_i h' h
      have := h x ?_ rfl; cases this
      rw [mem_iff_get?]
      simp only [get?_eq_getElem?]
    exact ⟨_, h₂⟩; exact ⟨_ , h₂.symm⟩

@[simp] theorem nodup_replicate {n : Nat} {a : α} :
    (replicate n a).Nodup ↔ n ≤ 1 := by simp [Nodup]

end List
