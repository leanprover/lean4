/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

prelude
public import Init.Data.List.Lemmas
public import Init.Data.List.Pairwise
public import Init.Data.Order.Factories
import Init.Data.Order.Lemmas

public section

open Std

/-!
# Lemmas about `List.min?` and `List.max?.
-/

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

open Nat

/-! ## Minima and maxima -/

/-! ### min? -/

@[simp] theorem min?_nil [Min α] : ([] : List α).min? = none := rfl

-- We don't put `@[simp]` on `min?_cons'`,
-- because the definition in terms of `foldl` is not useful for proofs.
theorem min?_cons' [Min α] {xs : List α} : (x :: xs).min? = some (foldl min x xs) := rfl

@[simp] theorem min?_cons [Min α] [Std.Associative (min : α → α → α)] {xs : List α} :
    (x :: xs).min? = some (xs.min?.elim x (min x)) := by
  cases xs <;> simp [min?_cons', foldl_assoc]

@[simp] theorem min?_eq_none_iff {xs : List α} [Min α] : xs.min? = none ↔ xs = [] := by
  cases xs <;> simp [min?]

theorem isSome_min?_of_mem {l : List α} [Min α] {a : α} (h : a ∈ l) :
    l.min?.isSome := by
  cases l <;> simp_all [min?_cons']

theorem min?_eq_head? {α : Type u} [Min α] {l : List α}
    (h : l.Pairwise (fun a b => min a b = a)) : l.min? = l.head? := by
  cases l with
  | nil => rfl
  | cons x l =>
    rw [head?_cons, min?_cons', Option.some.injEq]
    induction l generalizing x with
    | nil => simp
    | cons y l ih =>
      have hx : min x y = x := rel_of_pairwise_cons h mem_cons_self
      rw [foldl_cons, ih _ (hx.symm ▸ h.sublist (by simp)), hx]

theorem min?_mem [Min α] [MinEqOr α] :
    {xs : List α} → xs.min? = some a → a ∈ xs := by
  intro xs
  match xs with
  | nil => simp
  | x :: xs =>
    simp only [min?_cons', Option.some.injEq, mem_cons]
    intro eq
    induction xs generalizing x with
    | nil =>
      simp at eq
      simp [eq]
    | cons y xs ind =>
      simp at eq
      have p := ind _ eq
      cases p with
      | inl p =>
        cases MinEqOr.min_eq_or x y with | _ q => simp [p, q]
      | inr p => simp [p, mem_cons]

-- TODO: update this
-- See also `Init.Data.List.Nat.Basic` for specialisations of the next two results to `Nat`.

theorem le_min?_iff [Min α] [LE α] [OrderData α] [LawfulOrderInf α] [LawfulOrderLE α] :
    {xs : List α} → xs.min? = some a → ∀ {x}, x ≤ a ↔ ∀ b, b ∈ xs → x ≤ b
  | nil => by simp
  | cons x xs => by
    rw [min?]
    intro eq y
    simp only [Option.some.injEq] at eq
    induction xs generalizing x with
    | nil =>
      simp at eq
      simp [eq]
    | cons z xs ih =>
      simp at eq
      simp [ih _ eq, le_min_iff, and_assoc]

theorem min?_eq_some_iff [Min α] [LE α] {xs : List α} [OrderData α] [LinearOrder (α)]
    [LawfulOrderMin α] [LawfulOrderLE α] : xs.min? = some a ↔ a ∈ xs ∧ ∀ b, b ∈ xs → a ≤ b := by
  refine ⟨fun h => ⟨min?_mem h, (le_min?_iff h).1 (le_refl _)⟩, ?_⟩
  intro ⟨h₁, h₂⟩
  cases xs with
  | nil => simp at h₁
  | cons x xs =>
    rw [List.min?]
    exact congrArg some <| le_antisymm
      ((le_min?_iff (xs := x :: xs) rfl).1 (le_refl _) _ h₁)
      (h₂ _ (min?_mem (xs := x :: xs) rfl))

private theorem min?_attach [Min α] [MinEqOr α] {xs : List α} :
    xs.attach.min? = (xs.min?.pmap (fun m hm => ⟨m, min?_mem hm⟩) (fun _ => id)) := by
  cases xs with
  | nil => simp
  | cons x xs =>
    simp only [min?, attach_cons, Option.some.injEq, Option.pmap_some]
    rw [foldl_map]
    simp only [Subtype.ext_iff]
    rw [← foldl_attach (l := xs)]
    apply Eq.trans (foldl_hom (f := Subtype.val) ?_).symm
    · rfl
    · intros; rfl

private theorem min?_eq_min?_attach [Min α] [MinEqOr α] {xs : List α} :
    xs.min? = (xs.attach.min?.map Subtype.val) := by
  simp [min?_attach, Option.map_pmap]

private theorem min?_eq_some_iff_subtype [Min α] [LE α] {xs : List α} [OrderData α]
    [MinEqOr α] [LinearOrder (Subtype (· ∈ xs))]
    [LawfulOrderMin (Subtype (· ∈ xs))] [LawfulOrderLE (Subtype (· ∈ xs))] :
    xs.min? = some a ↔ a ∈ xs ∧ ∀ b, b ∈ xs → a ≤ b := by
  have := fun a => min?_eq_some_iff (xs := xs.attach) (a := a)
  rw [min?_eq_min?_attach]
  simp [min?_eq_some_iff]
  constructor
  · rintro ⟨ha, h⟩
    exact ⟨ha, h⟩
  · rintro ⟨ha, h⟩
    exact ⟨ha, h⟩

theorem min?_eq_some_iff_legacy [Min α] [LE α]
    (le_refl : ∀ a : α, a ≤ a)
    (min_eq_or : ∀ a b : α, min a b = a ∨ min a b = b)
    (le_min_iff : ∀ a b c : α, a ≤ min b c ↔ a ≤ b ∧ a ≤ c) {xs : List α}
    (anti : ∀ a b, a ∈ xs → b ∈ xs → a ≤ b → b ≤ a → a = b := by
      exact fun a b _ _ => Std.Antisymm.antisymm a b) :
    xs.min? = some a ↔ a ∈ xs ∧ ∀ b, b ∈ xs → a ≤ b := by
  -- TODO: Extract the order on Subtype (· ∈ xs) into separate declarations so that they can
  -- be reused
  letI : OrderData α := .ofLE α
  haveI : MinEqOr α := ⟨min_eq_or⟩
  haveI : LinearOrder (Subtype (· ∈ xs)) := by
    refine .ofLE ?_ ?_ ?_
    · exact fun a b hab hba => Subtype.ext <| anti a.val b.val a.property b.property hab hba
    · intro a b c hab hbc
      have : min b.val c.val = b.val := by
        apply anti _ _ (MinEqOr.elim b.property c.property) b.property
        · exact ((le_min_iff (min b.val c.val) _ _).mp (le_refl _)).1
        · exact MinEqOr.elim (le_refl _) hbc
      specialize le_min_iff a b c
      rw [this] at le_min_iff
      exact (le_min_iff.mp hab).2
    · exact fun a b => by
        cases min_eq_or a.val b.val
        case inl h => exact Or.inl ((h ▸ le_min_iff a.val a.val b.val).mp (le_refl _)).2
        case inr h => exact Or.inr ((h ▸ le_min_iff b.val a.val b.val).mp (le_refl _)).1
  haveI : LawfulOrderInf (Subtype (· ∈ xs)) := by
    refine ⟨fun a b c => ?_⟩
    simpa [OrderData.IsLE, LawfulOrderLE.le_iff] using le_min_iff a b c
  haveI : MinEqOr (Subtype (· ∈ xs)) := by
    refine ⟨fun a b => ?_⟩
    simpa [Min.min, Subtype.ext_iff] using min_eq_or a b
  haveI : LawfulOrderMin (Subtype (· ∈ xs)) := ⟨⟩
  exact min?_eq_some_iff_subtype (α := α) (xs := xs) (a := a)

theorem min?_replicate [Min α] [Std.IdempotentOp (min : α → α → α)] {n : Nat} {a : α} :
    (replicate n a).min? = if n = 0 then none else some a := by
  induction n with
  | zero => rfl
  | succ n ih => cases n <;> simp_all [replicate_succ, min?_cons', Std.IdempotentOp.idempotent]

@[simp] theorem min?_replicate_of_pos [Min α] [MinEqOr α] {n : Nat} {a : α} (h : 0 < n) :
    (replicate n a).min? = some a := by
  simp [min?_replicate, Nat.ne_of_gt h]

/--
Requirements are satisfied for `[OrderData α] [Min α] [LinearOrder α] [LawfulOrderMin α]`
-/
theorem foldl_min [Min α] [Std.IdempotentOp (min : α → α → α)] [Std.Associative (min : α → α → α)]
    {l : List α} {a : α} : l.foldl (init := a) min = min a (l.min?.getD a) := by
  cases l <;> simp [min?, foldl_assoc, Std.IdempotentOp.idempotent]

/-! ### max? -/

@[simp] theorem max?_nil [Max α] : ([] : List α).max? = none := rfl

-- We don't put `@[simp]` on `max?_cons'`,
-- because the definition in terms of `foldl` is not useful for proofs.
theorem max?_cons' [Max α] {xs : List α} : (x :: xs).max? = some (foldl max x xs) := rfl

@[simp] theorem max?_cons [Max α] [Std.Associative (max : α → α → α)] {xs : List α} :
    (x :: xs).max? = some (xs.max?.elim x (max x)) := by
  cases xs <;> simp [max?_cons', foldl_assoc]

@[simp] theorem max?_eq_none_iff {xs : List α} [Max α] : xs.max? = none ↔ xs = [] := by
  cases xs <;> simp [max?]

theorem isSome_max?_of_mem {l : List α} [Max α] {a : α} (h : a ∈ l) :
    l.max?.isSome := by
  cases l <;> simp_all [max?_cons']

theorem max?_eq_head? {α : Type u} [Max α] {l : List α}
    (h : l.Pairwise (fun a b => max a b = a)) : l.max? = l.head? := by
  cases l with
  | nil => rfl
  | cons x l =>
    rw [head?_cons, max?_cons', Option.some.injEq]
    induction l generalizing x with
    | nil => simp
    | cons y l ih =>
      have hx : max x y = x := rel_of_pairwise_cons h mem_cons_self
      rw [foldl_cons, ih _ (hx.symm ▸ h.sublist (by simp)), hx]

theorem max?_mem [Max α] [MaxEqOr α] :
    {xs : List α} → xs.max? = some a → a ∈ xs := by
  intro xs
  match xs with
  | nil => simp
  | x :: xs =>
    simp only [max?_cons', Option.some.injEq, mem_cons]
    intro eq
    induction xs generalizing x with
    | nil =>
      simp at eq
      simp [eq]
    | cons y xs ind =>
      simp at eq
      have p := ind _ eq
      cases p with
      | inl p =>
        cases MaxEqOr.max_eq_or x y with | _ q => simp [p, q]
      | inr p => simp [p, mem_cons]

-- TODO: update this
-- See also `Init.Data.List.Nat.Basic` for specialisations of the next two results to `Nat`.

theorem max?_le_iff [Max α] [LE α] [OrderData α] [LawfulOrderSup α] [LawfulOrderLE α] :
    {xs : List α} → xs.max? = some a → ∀ {x}, a ≤ x ↔ ∀ b, b ∈ xs → b ≤ x
  | nil => by simp
  | cons x xs => by
    rw [max?]
    intro eq y
    simp only [Option.some.injEq] at eq
    induction xs generalizing x with
    | nil =>
      simp at eq
      simp [eq]
    | cons z xs ih =>
      simp at eq
      simp [ih _ eq, max_le_iff, and_assoc]

theorem max?_eq_some_iff [Max α] [LE α] {xs : List α} [OrderData α] [LinearOrder (α)]
    [LawfulOrderMax α] [LawfulOrderLE α] : xs.max? = some a ↔ a ∈ xs ∧ ∀ b, b ∈ xs → b ≤ a := by
  refine ⟨fun h => ⟨max?_mem h, (max?_le_iff h).1 (le_refl _)⟩, ?_⟩
  intro ⟨h₁, h₂⟩
  cases xs with
  | nil => simp at h₁
  | cons x xs =>
    rw [List.max?]
    exact congrArg some <| le_antisymm
      (h₂ _ (max?_mem (xs := x :: xs) rfl))
      ((max?_le_iff (xs := x :: xs) rfl).1 (le_refl _) _ h₁)

private theorem max?_attach [Max α] [MaxEqOr α] {xs : List α} :
    xs.attach.max? = (xs.max?.pmap (fun m hm => ⟨m, max?_mem hm⟩) (fun _ => id)) := by
  cases xs with
  | nil => simp
  | cons x xs =>
    simp only [max?, attach_cons, Option.some.injEq, Option.pmap_some]
    rw [foldl_map]
    simp only [Subtype.ext_iff]
    rw [← foldl_attach (l := xs)]
    apply Eq.trans (foldl_hom (f := Subtype.val) ?_).symm
    · rfl
    · intros; rfl

private theorem max?_eq_max?_attach [Max α] [MaxEqOr α] {xs : List α} :
    xs.max? = (xs.attach.max?.map Subtype.val) := by
  simp [max?_attach, Option.map_pmap]

private theorem max?_eq_some_iff_subtype [Max α] [LE α] {xs : List α} [OrderData α]
    [MaxEqOr α] [LinearOrder (Subtype (· ∈ xs))]
    [LawfulOrderMax (Subtype (· ∈ xs))] [LawfulOrderLE (Subtype (· ∈ xs))] :
    xs.max? = some a ↔ a ∈ xs ∧ ∀ b, b ∈ xs → b ≤ a := by
  have := fun a => max?_eq_some_iff (xs := xs.attach) (a := a)
  rw [max?_eq_max?_attach]
  simp [max?_eq_some_iff]
  constructor
  · rintro ⟨ha, h⟩
    exact ⟨ha, h⟩
  · rintro ⟨ha, h⟩
    exact ⟨ha, h⟩

theorem max?_eq_some_iff_legacy [Max α] [LE α] [anti : Std.Antisymm (· ≤ · : α → α → Prop)]
    (le_refl : ∀ a : α, a ≤ a)
    (max_eq_or : ∀ a b : α, max a b = a ∨ max a b = b)
    (max_le_iff : ∀ a b c : α, max b c ≤ a ↔ b ≤ a ∧ c ≤ a) {xs : List α} :
    xs.max? = some a ↔ a ∈ xs ∧ ∀ b ∈ xs, b ≤ a := by
  letI : OrderData α := .ofLE α
  haveI : MaxEqOr α := ⟨max_eq_or⟩
  haveI : LinearOrder α := by
    refine .ofLE ?_ ?_ ?_
    · exact anti.antisymm
    · intro a b c hab hbc
      have : max a b = b := by
        apply anti.antisymm _ _
        · refine MaxEqOr.elim (P := (· ≤ b)) hab (le_refl _)
        · exact ((max_le_iff _ _ _).mp (le_refl _)).2
      specialize max_le_iff c a b
      rw [this] at max_le_iff
      exact (max_le_iff.mp hbc).1
    · exact fun a b => by
        cases max_eq_or a b
        case inl h => exact Or.inr ((h ▸ max_le_iff a a b).mp (le_refl _)).2
        case inr h => exact Or.inl ((h ▸ max_le_iff b a b).mp (le_refl _)).1
  haveI : LawfulOrderSup α := by
    refine ⟨fun a b c => ?_⟩
    simpa [OrderData.IsLE, LawfulOrderLE.le_iff] using max_le_iff c a b
  haveI : MaxEqOr (Subtype (· ∈ xs)) := by
    refine ⟨fun a b => ?_⟩
    simpa [Max.max, Subtype.ext_iff] using max_eq_or a b
  haveI : LawfulOrderMax α := ⟨⟩
  apply max?_eq_some_iff

theorem max?_replicate [Max α] [Std.IdempotentOp (max : α → α → α)] {n : Nat} {a : α} :
    (replicate n a).max? = if n = 0 then none else some a := by
  induction n with
  | zero => rfl
  | succ n ih => cases n <;> simp_all [replicate_succ, max?_cons', Std.IdempotentOp.idempotent]

@[simp] theorem max?_replicate_of_pos [Max α] [MaxEqOr α] {n : Nat} {a : α} (h : 0 < n) :
    (replicate n a).max? = some a := by
  simp [max?_replicate, Nat.ne_of_gt h]

/--
Requirements are satisfied for `[OrderData α] [Max α] [LinearOrder α] [LawfulOrderMax α]`
-/
theorem foldl_max [Max α] [Std.IdempotentOp (max : α → α → α)] [Std.Associative (max : α → α → α)]
    {l : List α} {a : α} : l.foldl (init := a) max = max a (l.max?.getD a) := by
  cases l <;> simp [max?, foldl_assoc, Std.IdempotentOp.idempotent]

end List
