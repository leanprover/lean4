module

prelude
public import Std.Classes.Ord.New.Classes
import Init.SimpLemmas
import Init.Classical

/-!
This module provides typeclass instances and lemmas about order-related typeclasses such as
`LE` and `OrderData`.
-/

public instance {α : Type u} [LE α] {P : α → Prop} : LE (Subtype P) where
  le a b := a.val ≤ b.val

public instance {α : Type u} [OrderData α] {P : α → Prop} : OrderData (Subtype P) where
  IsLE a b := OrderData.IsLE a.val b.val

public instance {α : Type u} [LE α] [OrderData α] [LawfulOrderLE α] [PartialOrder α] :
    Std.Antisymm (fun a b : α => a ≤ b) where
  antisymm a b := by
    simp only [LawfulOrderLE.le_iff]
    apply PartialOrder.le_antisymm

public instance {α : Type u} [LE α] [OrderData α] [LawfulOrderLE α] [Preorder α] :
    Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·) where
  trans := by simpa [LawfulOrderLE.le_iff] using fun {a b c} => Preorder.le_trans a b c

public instance {α : Type u} [LE α] [OrderData α] [LawfulOrderLE α] [Preorder α] :
    Std.Refl (α := α) (· ≤ ·) where
  refl a := by simpa [LawfulOrderLE.le_iff] using Preorder.le_refl a

public instance {α : Type u} [LE α] [OrderData α] [LawfulOrderLE α] [LinearPreorder α] :
    Std.Total (α := α) (· ≤ ·) where
  total a b := by simpa [LawfulOrderLE.le_iff] using LinearPreorder.le_total a b

section LE

public theorem le_refl {α : Type u} [LE α] [OrderData α] [LawfulOrderLE α] [Preorder α] (a : α) :
    a ≤ a := by
  simp [LawfulOrderLE.le_iff, Preorder.le_refl]

public theorem le_antisymm {α : Type u} [LE α] [Std.Antisymm (α := α) (· ≤ ·)] {a b : α}
    (hab : a ≤ b) (hba : b ≤ a) : a = b :=
  Std.Antisymm.antisymm _ _ hab hba

public theorem le_trans {α : Type u} [LE α] [Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·)] {a b c : α}
    (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  Trans.trans hab hbc

public theorem le_total {α : Type u} [LE α] [Std.Total (α := α) (· ≤ ·)] {a b : α} :
    a ≤ b ∨ b ≤ a :=
  Std.Total.total a b

public scoped instance Classical.Order.instLE {α : Type u} [OrderData α] :
    LE α where
  le a b := OrderData.IsLE a b

open Classical.Order in
public instance Classical.Order.instLawfulOrderLE {α : Type u} [OrderData α] :
    LawfulOrderLE α where
  le_iff _ _ := Iff.rfl

end LE

section LT

public theorem lt_iff_le_and_not_ge {α : Type u} [LT α] [LE α] [OrderData α] [LawfulOrderLE α]
    [LawfulOrderLT α] {a b : α} :
    a < b ↔ a ≤ b ∧ ¬ b ≤ a := by
  simp [LawfulOrderLE.le_iff, LawfulOrderLT.lt_iff]

public theorem not_lt {α : Type u} [LT α] [LE α] [OrderData α] [Std.Total (α := α) (· ≤ ·)]
    [LawfulOrderLE α] [LawfulOrderLT α] {a b : α} :
    ¬ a < b ↔ b ≤ a := by
  simp [lt_iff_le_and_not_ge, Classical.not_not, Std.Total.total]

public instance {α : Type u} [LT α] [OrderData α] [LawfulOrderLT α] :
    Std.Asymm (α := α) (· < ·) where
  asymm a b := by
    simp only [LawfulOrderLT.lt_iff]
    intro h h'
    exact h.2.elim h'.1

-- TODO: derive from reflexivity of LE?
public instance {α : Type u} [LT α] [OrderData α] [Preorder α] [LawfulOrderLT α] :
    Std.Irrefl (α := α) (· < ·) where
  irrefl a b := by simp [LawfulOrderLT.lt_iff] at b

public instance {α : Type u} [LT α] [OrderData α]
    [open Classical.Order in Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·) ] [LawfulOrderLT α] :
    Trans (α := α) (· < ·) (· < ·) (· < ·) where
  trans {a b c} hab hbc := by
    open Classical.Order in
    simp only [lt_iff_le_and_not_ge] at hab hbc ⊢
    apply And.intro
    · exact le_trans hab.1 hbc.1
    · intro hca
      exact hab.2.elim (le_trans hbc.1 hca)

public instance {α : Type u} {_ : LT α} [OrderData α] [LawfulOrderLT α]
    [open Classical.Order in Std.Total (α := α) (· ≤ ·)]
    [open Classical.Order in Std.Antisymm (α := α) (· ≤ ·)] :
    Std.Antisymm (α := α) (¬ · < ·) where
  antisymm a b hab hba := by
    open Classical.Order in
    simp only [not_lt] at hab hba
    exact Std.Antisymm.antisymm (r := (· ≤ ·)) a b hba hab

public instance {α : Type u} {_ : LT α} [OrderData α] [LawfulOrderLT α]
    [open Classical.Order in Std.Total (α := α) (· ≤ ·)]
    [open Classical.Order in Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·)] :
    Trans (α := α) (¬ · < ·) (¬ · < ·) (¬ · < ·) where
  trans {a b c} hab hbc := by
    open Classical.Order in
    simp only [not_lt] at hab hbc ⊢
    exact le_trans hbc hab

public instance {α : Type u} {_ : LT α} [OrderData α] [LawfulOrderLT α]
    [open Classical.Order in Std.Total (α := α) (· ≤ ·)] :
    Std.Total (α := α) (¬ · < ·) where
  total a b := by
    open Classical.Order in
    simp [not_lt, Std.Total.total]

public theorem lt_of_le_of_lt {α : Type u} [LE α] [LT α] [OrderData α]
    [Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·)]
    [LawfulOrderLT α] [LawfulOrderLE α] {a b c : α} (hab : a ≤ b) (hbc : b < c) :
    a < c := by
  simp only [lt_iff_le_and_not_ge] at hbc ⊢
  apply And.intro
  · exact le_trans hab hbc.1
  · intro hca
    exact hbc.2.elim (le_trans hca hab)

public theorem lt_of_le_of_ne {α : Type u} [LE α] [LT α] [OrderData α]
    [Std.Antisymm (α := α) (· ≤ ·)] [LawfulOrderLT α] [LawfulOrderLE α] {a b : α}
    (hle : a ≤ b) (hne : a ≠ b) : a < b := by
  apply Classical.byContradiction
  simp only [lt_iff_le_and_not_ge, hle, true_and, Classical.not_not, imp_false]
  intro hge
  exact hne.elim <| Std.Antisymm.antisymm a b hle hge

end LT

section Min

/--
If both `a` and `b` satisfy some property `P`, then so does `min a b`, because it is equal to
either `a` or `b`.
-/
public def MinEqOr.elim {α : Type u} [Min α] [MinEqOr α] {P : α → Prop} {a b : α} (ha : P a) (hb : P b) :
    P (min a b) := by
  cases MinEqOr.min_eq_or a b <;> simp_all

public theorem min_self {α : Type u} [Min α] [Std.IdempotentOp (min : α → α → α)] {a : α} :
    min a a = a :=
  Std.IdempotentOp.idempotent a

public theorem le_min_iff {α : Type u} [Min α] [LE α] [OrderData α]
    [LawfulOrderLE α] [LawfulOrderInf α] {a b c : α} :
    a ≤ min b c ↔ a ≤ b ∧ a ≤ c := by
  simpa [LawfulOrderLE.le_iff] using LawfulOrderInf.le_min_iff a b c

public theorem min_le_left {α : Type u} [Min α] [LE α] [OrderData α] [Preorder α]
    [LawfulOrderLE α] [LawfulOrderInf α] {a b : α} :
    min a b ≤ a :=
  le_min_iff.mp (le_refl _) |>.1

public theorem min_le_right {α : Type u} [Min α] [LE α] [OrderData α] [Preorder α]
    [LawfulOrderLE α] [LawfulOrderInf α] {a b : α} :
    min a b ≤ b :=
  le_min_iff.mp (le_refl _) |>.2

public theorem min_le {α : Type u} [Min α] [LE α] [OrderData α] [Preorder α]
    [LawfulOrderLE α] [LawfulOrderMin α] {a b c : α} :
    min a b ≤ c ↔ a ≤ c ∨ b ≤ c := by
  cases MinEqOr.min_eq_or a b <;> rename_i h
  · simpa [h] using le_trans (h ▸ min_le_right (a := a) (b := b))
  · simpa [h] using le_trans (h ▸ min_le_left (a := a) (b := b))

public instance {α : Type u} [Min α] [MinEqOr α] {P : α → Prop} : Min (Subtype P) where
  min a b := ⟨Min.min a.val b.val, MinEqOr.elim a.property b.property⟩

public instance {α : Type u} [LE α] {P : α → Prop} : LE (Subtype P) where
  le a b := a.val ≤ b.val

public instance {α : Type u} [Min α] [MinEqOr α] :
    Std.IdempotentOp (min : α → α → α) where
  idempotent a := by cases MinEqOr.min_eq_or a a <;> assumption

open Classical.Order in
public instance {α : Type u} [OrderData α] [Min α] [LinearOrder α] [LawfulOrderMin α] :
    Std.Associative (min : α → α → α) where
  assoc a b c := by apply le_antisymm <;> simp [min_le, le_min_iff, le_refl]

public instance {α : Type u} [LE α] [OrderData α] [LawfulOrderLE α]
    {P : α → Prop} : LawfulOrderLE (Subtype P) where
  le_iff a b := by simp [LE.le, OrderData.IsLE, LawfulOrderLE.le_iff]

public theorem min_eq_or {α : Type u} [Min α] [MinEqOr α] {a b : α} :
    min a b = a ∨ min a b = b :=
  MinEqOr.min_eq_or a b

end Min

section Max

/--
If both `a` and `b` satisfy some property `P`, then so does `max a b`, because it is equal to
either `a` or `b`.
-/
public def MaxEqOr.elim {α : Type u} [Max α] [MaxEqOr α] {P : α → Prop} {a b : α} (ha : P a) (hb : P b) :
    P (max a b) := by
  cases MaxEqOr.max_eq_or a b <;> simp_all

public theorem max_self {α : Type u} [Max α] [Std.IdempotentOp (max : α → α → α)] {a : α} :
    max a a = a :=
  Std.IdempotentOp.idempotent a

public theorem max_le_iff {α : Type u} [Max α] [LE α] [OrderData α]
    [LawfulOrderLE α] [LawfulOrderSup α] {a b c : α} :
    max a b ≤ c ↔ a ≤ c ∧ b ≤ c := by
  simpa [LawfulOrderLE.le_iff] using LawfulOrderSup.max_le_iff a b c

public theorem left_le_max {α : Type u} [Max α] [LE α] [OrderData α] [Preorder α]
    [LawfulOrderLE α] [LawfulOrderSup α] {a b : α} :
    a ≤ max a b :=
  max_le_iff.mp (le_refl _) |>.1

public theorem right_le_max {α : Type u} [Max α] [LE α] [OrderData α] [Preorder α]
    [LawfulOrderLE α] [LawfulOrderSup α] {a b : α} :
    b ≤ max a b :=
  max_le_iff.mp (le_refl _) |>.2

public theorem le_max {α : Type u} [Max α] [LE α] [OrderData α] [Preorder α]
    [LawfulOrderLE α] [LawfulOrderMax α] {a b c : α} :
    a ≤ max b c ↔ a ≤ b ∨ a ≤ c := by
  cases MaxEqOr.max_eq_or b c <;> rename_i h
  · simpa [h] using (le_trans · (h ▸ right_le_max))
  · simpa [h] using (le_trans · (h ▸ left_le_max))

public instance {α : Type u} [Max α] [MaxEqOr α] {P : α → Prop} : Max (Subtype P) where
  max a b := ⟨Max.max a.val b.val, MaxEqOr.elim a.property b.property⟩

public instance {α : Type u} [Max α] [MaxEqOr α] :
    Std.IdempotentOp (max : α → α → α) where
  idempotent a := by cases MaxEqOr.max_eq_or a a <;> assumption

open Classical.Order in
public instance {α : Type u} [OrderData α] [Max α] [LinearOrder α] [LawfulOrderMax α] :
    Std.Associative (max : α → α → α) where
  assoc a b c := by
    apply le_antisymm
    all_goals
      simp only [max_le_iff]
      simp [le_max, le_refl]

public theorem max_eq_or {α : Type u} [Max α] [MaxEqOr α] {a b : α} :
    max a b = a ∨ max a b = b :=
  MaxEqOr.max_eq_or a b

end Max
