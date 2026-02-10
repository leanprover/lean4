/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

prelude
public import Init.Data.Subtype.Order
import Init.Data.Order.Lemmas
public import Init.Data.List.Attach
import Init.Data.Bool
import Init.Data.List.Pairwise
import Init.Data.List.Sublist
import Init.Data.Option.Lemmas
import Init.Data.Subtype.Basic

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

@[simp, grind =] theorem min?_nil [Min α] : ([] : List α).min? = none := rfl

@[simp, grind =]
public theorem min?_singleton [Min α] {x : α} : [x].min? = some x :=
  (rfl)

-- We don't put `@[simp]` on `min?_cons'`,
-- because the definition in terms of `foldl` is not useful for proofs.
theorem min?_cons' [Min α] {xs : List α} : (x :: xs).min? = some (foldl min x xs) := rfl

@[simp] theorem min?_cons [Min α] [Std.Associative (min : α → α → α)] {xs : List α} :
    (x :: xs).min? = some (xs.min?.elim x (min x)) := by
  cases xs <;> simp [min?_cons', foldl_assoc]

@[simp, grind =] theorem min?_eq_none_iff {xs : List α} [Min α] : xs.min? = none ↔ xs = [] := by
  cases xs <;> simp [min?]

@[simp, grind =]
public theorem isSome_min?_iff [Min α] {xs : List α} : xs.min?.isSome ↔ xs ≠ [] := by
  cases xs <;> simp [min?]

@[grind .]
theorem isSome_min?_of_mem {l : List α} [Min α] {a : α} (h : a ∈ l) :
    l.min?.isSome := by
  cases l <;> simp_all [min?_cons']

theorem isSome_min?_of_ne_nil [Min α] {l : List α} (hl : l ≠ []) : l.min?.isSome := by
  rwa [isSome_min?_iff]

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

theorem le_min?_iff [Min α] [LE α] [LawfulOrderInf α] :
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

theorem min?_eq_some_iff [Min α] [LE α] {xs : List α} [IsLinearOrder α] [LawfulOrderMin α] :
    xs.min? = some a ↔ a ∈ xs ∧ ∀ b, b ∈ xs → a ≤ b := by
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

theorem min?_eq_min?_attach [Min α] [MinEqOr α] {xs : List α} :
    xs.min? = (xs.attach.min?.map Subtype.val) := by
  simp [min?_attach, Option.map_pmap]

theorem min?_eq_some_iff_subtype [Min α] [LE α] {xs : List α}
    [MinEqOr α] [IsLinearOrder (Subtype (· ∈ xs))] [LawfulOrderMin (Subtype (· ∈ xs))] :
    xs.min? = some a ↔ a ∈ xs ∧ ∀ b, b ∈ xs → a ≤ b := by
  have := fun a => min?_eq_some_iff (xs := xs.attach) (a := a)
  rw [min?_eq_min?_attach]
  simp [min?_eq_some_iff]
  constructor
  · rintro ⟨ha, h⟩
    exact ⟨ha, h⟩
  · rintro ⟨ha, h⟩
    exact ⟨ha, h⟩

theorem min?_replicate [Min α] [Std.IdempotentOp (min : α → α → α)] {n : Nat} {a : α} :
    (replicate n a).min? = if n = 0 then none else some a := by
  induction n with
  | zero => rfl
  | succ n ih => cases n <;> simp_all [replicate_succ, min?_cons', Std.IdempotentOp.idempotent]

@[simp, grind =]
theorem min?_replicate_of_pos [Min α] [MinEqOr α] {n : Nat} {a : α} (h : 0 < n) :
    (replicate n a).min? = some a := by
  simp [min?_replicate, Nat.ne_of_gt h]

/--
This lemma is also applicable given the following instances:

```
[LE α] [Min α] [IsLinearOrder α] [LawfulOrderMin α]
```
-/
theorem foldl_min [Min α] [Std.IdempotentOp (min : α → α → α)] [Std.Associative (min : α → α → α)]
    {l : List α} {a : α} : l.foldl (init := a) min = min a (l.min?.getD a) := by
  cases l <;> simp [min?, foldl_assoc, Std.IdempotentOp.idempotent]

/-! ### min -/

@[simp, grind =]
theorem min_singleton [Min α] {x : α} :
    [x].min (cons_ne_nil _ _) = x := by
  (rfl)

theorem min?_eq_some_min [Min α] : {l : List α} → (hl : l ≠ []) →
    l.min? = some (l.min hl)
  | a::as, _ => by simp [List.min, List.min?_cons']

theorem min_eq_get_min? [Min α] : (l : List α) → (hl : l ≠ []) →
    l.min hl = l.min?.get (isSome_min?_of_ne_nil hl)
  | a::as, _ => by simp [List.min, List.min?_cons']

@[simp, grind =]
theorem get_min? [Min α] {l : List α} {h : l.min?.isSome} :
    l.min?.get h = l.min (isSome_min?_iff.mp h) := by
  simp [min?_eq_some_min (isSome_min?_iff.mp h)]

theorem min_eq_head {α : Type u} [Min α] {l : List α} (hl : l ≠ [])
    (h : l.Pairwise (fun a b => min a b = a)) : l.min hl = l.head hl := by
  apply Option.some.inj
  rw [← min?_eq_some_min, ← head?_eq_some_head]
  exact min?_eq_head? h

@[grind .]
theorem min_mem [Min α] [MinEqOr α] {l : List α} (hl : l ≠ []) : l.min hl ∈ l :=
  min?_mem (min?_eq_some_min hl)

@[grind .]
theorem min_le_of_mem [Min α] [LE α] [Std.IsLinearOrder α] [Std.LawfulOrderMin α]
    {l : List α} {a : α} (ha : a ∈ l) :
    l.min (ne_nil_of_mem ha) ≤ a :=
  (min?_eq_some_iff.mp (min?_eq_some_min (List.ne_nil_of_mem ha))).right a ha

protected theorem le_min_iff [Min α] [LE α] [LawfulOrderInf α]
    {l : List α} (hl : l ≠ []) : ∀ {x}, x ≤ l.min hl ↔ ∀ b, b ∈ l → x ≤ b :=
  le_min?_iff (min?_eq_some_min hl)

theorem min_eq_iff [Min α] [LE α] {l : List α} [IsLinearOrder α] [LawfulOrderMin α] (hl : l ≠ []) :
    l.min hl = a ↔ a ∈ l ∧ ∀ b, b ∈ l → a ≤ b := by
  simpa [min?_eq_some_min hl] using (min?_eq_some_iff (xs := l))

@[simp, grind =] theorem min_replicate [Min α] [MinEqOr α] {n : Nat} {a : α} (h : replicate n a ≠ []) :
    (replicate n a).min h = a := by
  have n_pos : 0 < n := Nat.pos_of_ne_zero (fun hn => by simp [hn] at h)
  simpa [min?_eq_some_min h] using (min?_replicate_of_pos (a := a) n_pos)

theorem foldl_min_eq_min [Min α] [Std.IdempotentOp (min : α → α → α)] [Std.Associative (min : α → α → α)]
    {l : List α} (hl : l ≠ []) {a : α} :
    l.foldl min a = min a (l.min hl) := by
  simpa [min?_eq_some_min hl] using foldl_min (l := l)

/-! ### max? -/

@[simp, grind =] theorem max?_nil [Max α] : ([] : List α).max? = none := rfl

@[simp, grind =]
public theorem max?_singleton [Max α] {x : α} : [x].max? = some x :=
  (rfl)

-- We don't put `@[simp]` on `max?_cons'`,
-- because the definition in terms of `foldl` is not useful for proofs.
theorem max?_cons' [Max α] {xs : List α} : (x :: xs).max? = some (foldl max x xs) := rfl

@[simp] theorem max?_cons [Max α] [Std.Associative (max : α → α → α)] {xs : List α} :
    (x :: xs).max? = some (xs.max?.elim x (max x)) := by
  cases xs <;> simp [max?_cons', foldl_assoc]

@[simp, grind =] theorem max?_eq_none_iff {xs : List α} [Max α] : xs.max? = none ↔ xs = [] := by
  cases xs <;> simp [max?]

@[simp, grind =]
public theorem isSome_max?_iff [Max α] {xs : List α} : xs.max?.isSome ↔ xs ≠ [] := by
  cases xs <;> simp [max?]

@[grind .]
theorem isSome_max?_of_mem {l : List α} [Max α] {a : α} (h : a ∈ l) :
    l.max?.isSome := by
  cases l <;> simp_all [max?_cons']

theorem isSome_max?_of_ne_nil [Max α] {l : List α} (hl : l ≠ []) : l.max?.isSome := by
  rwa [isSome_max?_iff]

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

theorem max?_le_iff [Max α] [LE α] [LawfulOrderSup α] :
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

theorem max?_eq_some_iff [Max α] [LE α] {xs : List α} [IsLinearOrder (α)]
    [LawfulOrderMax α] : xs.max? = some a ↔ a ∈ xs ∧ ∀ b, b ∈ xs → b ≤ a := by
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

theorem max?_eq_max?_attach [Max α] [MaxEqOr α] {xs : List α} :
    xs.max? = (xs.attach.max?.map Subtype.val) := by
  simp [max?_attach, Option.map_pmap]

theorem max?_eq_some_iff_subtype [Max α] [LE α] {xs : List α}
    [MaxEqOr α] [IsLinearOrder (Subtype (· ∈ xs))]
    [LawfulOrderMax (Subtype (· ∈ xs))] :
    xs.max? = some a ↔ a ∈ xs ∧ ∀ b, b ∈ xs → b ≤ a := by
  have := fun a => max?_eq_some_iff (xs := xs.attach) (a := a)
  rw [max?_eq_max?_attach]
  simp [max?_eq_some_iff]
  constructor
  · rintro ⟨ha, h⟩
    exact ⟨ha, h⟩
  · rintro ⟨ha, h⟩
    exact ⟨ha, h⟩

@[deprecated max?_eq_some_iff (since := "2025-08-01")]
theorem max?_eq_some_iff_legacy [Max α] [LE α] [anti : Std.Antisymm (· ≤ · : α → α → Prop)]
    (le_refl : ∀ a : α, a ≤ a)
    (max_eq_or : ∀ a b : α, max a b = a ∨ max a b = b)
    (max_le_iff : ∀ a b c : α, max b c ≤ a ↔ b ≤ a ∧ c ≤ a) {xs : List α} :
    xs.max? = some a ↔ a ∈ xs ∧ ∀ b ∈ xs, b ≤ a := by
  haveI : MaxEqOr α := ⟨max_eq_or⟩
  haveI : LawfulOrderMax α := .of_max_le_iff (fun _ _ _ => max_le_iff _ _ _) max_eq_or
  haveI : Refl (α := α) (· ≤ ·) := ⟨le_refl⟩
  haveI : IsLinearOrder α := .of_refl_of_antisymm_of_lawfulOrderMax
  apply max?_eq_some_iff

theorem max?_replicate [Max α] [Std.IdempotentOp (max : α → α → α)] {n : Nat} {a : α} :
    (replicate n a).max? = if n = 0 then none else some a := by
  induction n with
  | zero => rfl
  | succ n ih => cases n <;> simp_all [replicate_succ, max?_cons', Std.IdempotentOp.idempotent]

@[simp, grind =]
theorem max?_replicate_of_pos [Max α] [MaxEqOr α] {n : Nat} {a : α} (h : 0 < n) :
    (replicate n a).max? = some a := by
  simp [max?_replicate, Nat.ne_of_gt h]

/--
This lemma is also applicable given the following instances:

```
[LE α] [Min α] [IsLinearOrder α] [LawfulOrderMax α]
```
-/
theorem foldl_max [Max α] [Std.IdempotentOp (max : α → α → α)] [Std.Associative (max : α → α → α)]
    {l : List α} {a : α} : l.foldl (init := a) max = max a (l.max?.getD a) := by
  cases l <;> simp [max?, foldl_assoc, Std.IdempotentOp.idempotent]

/-! ### max -/

@[simp, grind =]
theorem max_singleton [Max α] {x : α} :
    [x].max (cons_ne_nil _ _) = x := by
  (rfl)

theorem max?_eq_some_max [Max α] : {l : List α} → (hl : l ≠ []) →
    l.max? = some (l.max hl)
  | a::as, _ => by simp [List.max, List.max?_cons']

theorem max_eq_get_max? [Max α] : (l : List α) → (hl : l ≠ []) →
    l.max hl = l.max?.get (isSome_max?_of_ne_nil hl)
  | a::as, _ => by simp [List.max, List.max?_cons']

@[simp, grind =]
theorem get_max? [Max α] {l : List α} {h : l.max?.isSome} :
    l.max?.get h = l.max (isSome_max?_iff.mp h) := by
  simp [max?_eq_some_max (isSome_max?_iff.mp h)]

theorem max_eq_head {α : Type u} [Max α] {l : List α} (hl : l ≠ [])
    (h : l.Pairwise (fun a b => max a b = a)) : l.max hl = l.head hl := by
  apply Option.some.inj
  rw [← max?_eq_some_max, ← head?_eq_some_head]
  exact max?_eq_head? h

@[grind .]
theorem max_mem [Max α] [MaxEqOr α] {l : List α} (hl : l ≠ []) : l.max hl ∈ l :=
  max?_mem (max?_eq_some_max hl)

protected theorem max_le_iff [Max α] [LE α] [LawfulOrderSup α]
    {l : List α} (hl : l ≠ []) : ∀ {x}, l.max hl ≤ x ↔ ∀ b, b ∈ l → b ≤ x :=
  max?_le_iff (max?_eq_some_max hl)

theorem max_eq_iff [Max α] [LE α] {l : List α} [IsLinearOrder α] [LawfulOrderMax α] (hl : l ≠ []) :
    l.max hl = a ↔ a ∈ l ∧ ∀ b, b ∈ l → b ≤ a := by
  simpa [max?_eq_some_max hl] using (max?_eq_some_iff (xs := l))

@[grind .]
theorem le_max_of_mem [Max α] [LE α] [Std.IsLinearOrder α] [Std.LawfulOrderMax α]
    {l : List α} {a : α} (ha : a ∈ l) :
    a ≤ l.max (List.ne_nil_of_mem ha) :=
  (max?_eq_some_iff.mp (max?_eq_some_max (List.ne_nil_of_mem ha))).right a ha

@[simp, grind =] theorem max_replicate [Max α] [MaxEqOr α] {n : Nat} {a : α} (h : replicate n a ≠ []) :
    (replicate n a).max h = a := by
  have n_pos : 0 < n := Nat.pos_of_ne_zero (fun hn => by simp [hn] at h)
  simpa [max?_eq_some_max h] using (max?_replicate_of_pos (a := a) n_pos)

theorem foldl_max_eq_max [Max α] [Std.IdempotentOp (max : α → α → α)] [Std.Associative (max : α → α → α)]
    {l : List α} (hl : l ≠ []) {a : α} :
    l.foldl max a = max a (l.max hl) := by
  simpa [max?_eq_some_max hl] using foldl_max (l := l)

end List
