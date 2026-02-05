/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Order.Factories
import all Init.Data.Order.Factories
public import Init.Classical
public import Init.Data.BEq
import Init.Data.Bool

namespace Std

/-!
This module provides typeclass instances and lemmas about order-related typeclasses.
-/

section AxiomaticInstances

public instance (r : α → α → Prop) [Asymm r] : Irrefl r where
  irrefl a h := Asymm.asymm a a h h

public instance (r : α → α → Prop) [Total r] : Refl r where
  refl a := by simpa using Total.total a a

public instance (r : α → α → Prop) [Asymm r] : Antisymm r where
  antisymm a b h h' := (Asymm.asymm a b h h').elim

public instance (r : α → α → Prop) [Total r] : Trichotomous r where
  trichotomous a b h h' := by simpa [h, h'] using Total.total (r := r) a b

public theorem Trichotomous.rel_or_eq_or_rel_swap {r : α → α → Prop} [i : Trichotomous r] {a b} :
    r a b ∨ a = b ∨ r b a := match Classical.em (r a b) with
  | .inl hab => .inl hab | .inr hab => match Classical.em (r b a) with
    | .inl hba => .inr <| .inr hba
    | .inr hba => .inr <| .inl <| i.trichotomous _ _ hab hba

public theorem trichotomous_of_rel_or_eq_or_rel_swap {r : α → α → Prop}
    (h : ∀ {a b}, r a b ∨ a = b ∨ r b a) : Trichotomous r where
  trichotomous _ _ hab hba := (h.resolve_left hab).resolve_right hba

public instance Antisymm.trichotomous_of_antisymm_not {r : α → α → Prop} [i : Antisymm (¬ r · ·)] :
    Trichotomous r where trichotomous := i.antisymm

public theorem Trichotomous.antisymm_not {r : α → α → Prop} [i : Trichotomous r] :
    Antisymm (¬ r · ·) where antisymm := i.trichotomous

public theorem Total.rel_of_not_rel_swap {r : α → α → Prop} [Total r] {a b} (h : ¬ r a b) : r b a :=
  (Total.total a b).elim (fun h' => (h h').elim) (·)

public theorem total_of_not_rel_swap_imp_rel {r : α → α → Prop} (h : ∀ {a b}, ¬ r a b → r b a) :
    Total r where
  total a b := match Classical.em (r a b) with | .inl hab => .inl hab | .inr hab => .inr (h hab)

public theorem total_of_refl_of_trichotomous (r : α → α → Prop) [Refl r] [Trichotomous r] :
    Total r where
  total a b := (Trichotomous.rel_or_eq_or_rel_swap (a := a) (b := b) (r := r)).elim Or.inl <|
    fun h => h.elim (fun h => h ▸ Or.inl (Refl.refl _)) Or.inr

public theorem asymm_of_irrefl_of_antisymm (r : α → α → Prop) [Irrefl r] [Antisymm r] :
    Asymm r where asymm a b h h' := Irrefl.irrefl _ (Antisymm.antisymm a b h h' ▸ h)

public instance Total.asymm_of_total_not {r : α → α → Prop} [i : Total (¬ r · ·)] : Asymm r where
  asymm a b h := (i.total a b).resolve_left (· h)

public theorem Asymm.total_not {r : α → α → Prop} [i : Asymm r] : Total (¬ r · ·) where
  total a b := match Classical.em (r b a) with
    | .inl hba => .inl <| i.asymm b a hba
    | .inr hba => .inr hba

public instance {α : Type u} [LE α] [IsPartialOrder α] :
    Antisymm (α := α) (· ≤ ·) where
  antisymm := IsPartialOrder.le_antisymm

public instance {α : Type u} [LE α] [IsPreorder α] :
    Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·) where
      trans := IsPreorder.le_trans _ _ _

public instance {α : Type u} [LE α] [IsPreorder α] :
    Refl (α := α) (· ≤ ·) where
  refl := IsPreorder.le_refl

public instance {α : Type u} [LE α] [IsLinearPreorder α] :
    Total (α := α) (· ≤ ·) where
  total := IsLinearPreorder.le_total

end AxiomaticInstances

section LE

@[simp]
public theorem le_refl {α : Type u} [LE α] [Refl (α := α) (· ≤ ·)] (a : α) : a ≤ a := by
  simp [Refl.refl]

public theorem le_of_eq [LE α] [Refl (α := α) (· ≤ ·)] {a b : α} : a = b → a ≤ b :=
  (· ▸ le_refl _)

public theorem le_antisymm {α : Type u} [LE α] [Std.Antisymm (α := α) (· ≤ ·)] {a b : α}
    (hab : a ≤ b) (hba : b ≤ a) : a = b :=
  Antisymm.antisymm _ _ hab hba

public theorem le_antisymm_iff {α : Type u} [LE α] [Antisymm (α := α) (· ≤ ·)]
    [Refl (α := α) (· ≤ ·)] {a b : α} : a ≤ b ∧ b ≤ a ↔ a = b :=
  ⟨fun | ⟨hab, hba⟩ => le_antisymm hab hba, by simp +contextual [le_refl]⟩

public theorem le_trans {α : Type u} [LE α] [Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·)] {a b c : α}
    (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  Trans.trans hab hbc

public theorem le_total {α : Type u} [LE α] [Std.Total (α := α) (· ≤ ·)] {a b : α} :
    a ≤ b ∨ b ≤ a :=
  Std.Total.total a b

public theorem le_of_not_ge {α : Type u} [LE α] [Std.Total (α := α) (· ≤ ·)] {a b : α} :
    ¬ b ≤ a → a ≤ b := Total.rel_of_not_rel_swap

end LE

section LT

public theorem lt_trans {α : Type u} [LT α] [Trans (α := α) (· < ·) (· < ·) (· < ·)] {a b c : α}
    (hab : a < b) (hbc : b < c) : a < c :=
  Trans.trans hab hbc

public theorem lt_iff_le_and_not_ge {α : Type u} [LT α] [LE α] [LawfulOrderLT α] {a b : α} :
    a < b ↔ a ≤ b ∧ ¬ b ≤ a :=
  LawfulOrderLT.lt_iff a b

public theorem not_lt_iff_not_le_or_ge {α : Type u} [LT α] [LE α] [LawfulOrderLT α]
    {a b : α} : ¬ a < b ↔ ¬ a ≤ b ∨ b ≤ a := by
  simp only [lt_iff_le_and_not_ge, Classical.not_and_iff_not_or_not, Classical.not_not]

public theorem not_le_of_gt {α : Type u} [LT α] [LE α] [LawfulOrderLT α] {a b : α}
    (h : a < b) : ¬ b ≤ a := (lt_iff_le_and_not_ge.1 h).2

public theorem not_lt_of_ge {α : Type u} [LT α] [LE α] [LawfulOrderLT α] {a b : α}
    (h : a ≤ b) : ¬ b < a := imp_not_comm.1 not_le_of_gt h

public instance {α : Type u} {_ : LE α} [LT α] [LawfulOrderLT α]
    [Trichotomous (α := α) (· < ·)] : Antisymm (α := α) (· ≤ ·) where
  antisymm _ _ hab hba := Trichotomous.trichotomous _ _ (not_lt_of_ge hba) (not_lt_of_ge hab)

public theorem not_gt_of_lt {α : Type u} [LT α] [i : Std.Asymm (α := α) (· < ·)] {a b : α}
    (h : a < b) : ¬ b < a :=
  i.asymm a b h

public theorem lt_irrefl {α : Type u} [LT α] [i : Std.Irrefl (α := α) (· < ·)] {a : α} :
    ¬ a < a :=
  i.irrefl a

public theorem le_of_lt {α : Type u} [LT α] [LE α] [LawfulOrderLT α] {a b : α} (h : a < b) :
    a ≤ b := (lt_iff_le_and_not_ge.1 h).1

public instance {α : Type u} {_ : LT α} [LE α] [LawfulOrderLT α]
    [Antisymm (α := α) (· ≤ ·)] : Antisymm (α := α) (· < ·) where
  antisymm _ _ hab hba := Antisymm.antisymm _ _ (le_of_lt hab) (le_of_lt hba)

public instance {α : Type u} [LT α] [LE α] [LawfulOrderLT α] :
    Std.Asymm (α := α) (· < ·) where
  asymm a b := by
    simp only [LawfulOrderLT.lt_iff]
    intro h h'
    exact h.2.elim h'.1

@[deprecated instIrreflOfAsymm (since := "2025-10-24")]
public theorem instIrreflLtOfIsPreorderOfLawfulOrderLT {α : Type u} [LT α] [LE α]
    [LawfulOrderLT α] : Std.Irrefl (α := α) (· < ·) := inferInstance

public instance {α : Type u} [LT α] [LE α] [Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·) ]
    [LawfulOrderLT α] : Trans (α := α) (· < ·) (· < ·) (· < ·) where
  trans {a b c} hab hbc := by
    simp only [lt_iff_le_and_not_ge] at hab hbc ⊢
    apply And.intro
    · exact le_trans hab.1 hbc.1
    · intro hca
      exact hab.2.elim (le_trans hbc.1 hca)

public theorem not_lt {α : Type u} [LT α] [LE α] [Std.Total (α := α) (· ≤ ·)] [LawfulOrderLT α]
    {a b : α} : ¬ a < b ↔ b ≤ a := by
  simp [not_lt_iff_not_le_or_ge]
  exact le_of_not_ge

public theorem not_le {α : Type u} [LT α] [LE α] [Std.Total (α := α) (· ≤ ·)] [LawfulOrderLT α]
    {a b : α} : ¬ a ≤ b ↔ b < a := by
  simp [lt_iff_le_and_not_ge]
  exact le_of_not_ge

public instance {α : Type u} {_ : LT α} [LE α] [LawfulOrderLT α]
    [Total (α := α) (· ≤ ·)] [Antisymm (α := α) (· ≤ ·)] : Trichotomous (α := α) (· < ·) where
  trichotomous a b hab hba := by
    simp only [not_lt] at hab hba
    exact Antisymm.antisymm (r := (· ≤ ·)) a b hba hab

public instance {α : Type u} {_ : LT α} [LE α] [LawfulOrderLT α]
    [Total (α := α) (· ≤ ·)] [Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·)] :
    Trans (α := α) (¬ · < ·) (¬ · < ·) (¬ · < ·) where
  trans {a b c} hab hbc := by
    simp only [not_lt] at hab hbc ⊢
    exact le_trans hbc hab

@[deprecated Asymm.total_not (since := "2025-10-24")]
public theorem instTotalNotLtOfLawfulOrderLTOfLe {α : Type u} {_ : LT α} [LE α] [LawfulOrderLT α]
    : Total (α := α) (¬ · < ·) := Asymm.total_not

public theorem lt_of_le_of_lt {α : Type u} [LE α] [LT α]
    [Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·)] [LawfulOrderLT α] {a b c : α} (hab : a ≤ b)
    (hbc : b < c) : a < c := by
  simp only [lt_iff_le_and_not_ge] at hbc ⊢
  apply And.intro
  · exact le_trans hab hbc.1
  · intro hca
    exact hbc.2.elim (le_trans hca hab)

public theorem lt_of_lt_of_le {α : Type u} [LE α] [LT α]
    [Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·)] [LawfulOrderLT α] {a b c : α} (hab : a < b)
    (hbc : b ≤ c) : a < c := by
  simp only [lt_iff_le_and_not_ge] at hab ⊢
  apply And.intro
  · exact le_trans hab.1 hbc
  · intro hca
    exact hab.2.elim (le_trans hbc hca)

public theorem lt_of_le_of_ne {α : Type u} [LE α] [LT α]
    [Std.Antisymm (α := α) (· ≤ ·)] [LawfulOrderLT α] {a b : α}
    (hle : a ≤ b) (hne : a ≠ b) : a < b := by
  apply Classical.byContradiction
  simp only [lt_iff_le_and_not_ge, hle, true_and, Classical.not_not, imp_false]
  intro hge
  exact hne.elim <| Std.Antisymm.antisymm a b hle hge

public theorem ne_of_lt {α : Type u} [LT α] [Std.Irrefl (α := α) (· < ·)] {a b : α} : a < b → a ≠ b :=
  fun h h' => absurd (h' ▸ h) (h' ▸ lt_irrefl)

public theorem le_iff_lt_or_eq [LE α] [LT α] [LawfulOrderLT α] [IsPartialOrder α] {a b : α} :
    a ≤ b ↔ a < b ∨ a = b := by
  refine ⟨fun h => ?_, fun h => h.elim le_of_lt le_of_eq⟩
  simp [Classical.or_iff_not_imp_left, Std.lt_iff_le_and_not_ge, h, ← Std.le_antisymm_iff]

public theorem lt_iff_le_and_ne [LE α] [LT α] [LawfulOrderLT α] [IsPartialOrder α] {a b : α} :
    a < b ↔ a ≤ b ∧ a ≠ b := by
  simpa [le_iff_lt_or_eq, or_and_right] using Std.ne_of_lt

end LT
end Std

namespace Classical.Order
open Std

public scoped instance instLT {α : Type u} [LE α] :
    LT α where
  lt a b := a ≤ b ∧ ¬ b ≤ a

public instance instLawfulOrderLT {α : Type u} [LE α] :
    LawfulOrderLT α where
  lt_iff _ _ := Iff.rfl

end Classical.Order

namespace Std
section BEq

public theorem beq_iff_le_and_ge {α : Type u} [BEq α] [LE α] [LawfulOrderBEq α]
    {a b : α} : a == b ↔ a ≤ b ∧ b ≤ a := by
  simp [LawfulOrderBEq.beq_iff_le_and_ge]

public instance {α : Type u} [BEq α] [LE α] [LawfulOrderBEq α] :
    Symm (α := α) (· == ·) where
  symm := by simp_all [beq_iff_le_and_ge]

public instance {α : Type u} [BEq α] [LE α] [LawfulOrderBEq α] [IsPreorder α] : EquivBEq α where
  rfl := by simp [beq_iff_le_and_ge, le_refl]
  symm := Symm.symm (r := (· == ·)) _ _
  trans hab hbc := by
    simp only [beq_iff_le_and_ge] at hab hbc ⊢
    exact ⟨le_trans hab.1 hbc.1, le_trans hbc.2 hab.2⟩

public instance {α : Type u} [BEq α] [LE α] [LawfulOrderBEq α] [IsPartialOrder α] :
    LawfulBEq α where
  eq_of_beq := by
    simp only [beq_iff_le_and_ge, and_imp]
    apply le_antisymm

end BEq
end Std

namespace Classical.Order
open Std

public noncomputable scoped instance instBEq {α : Type u} [LE α] : BEq α where
  beq a b := a ≤ b ∧ b ≤ a

public instance instLawfulOrderBEq {α : Type u} [LE α] :
    LawfulOrderBEq α where
  beq_iff_le_and_ge a b := by simp [BEq.beq]

end Classical.Order

namespace Std
section Min

public theorem min_self {α : Type u} [Min α] [Std.IdempotentOp (min : α → α → α)] {a : α} :
    min a a = a :=
  Std.IdempotentOp.idempotent a

public theorem le_min_iff {α : Type u} [Min α] [LE α]
    [LawfulOrderInf α] {a b c : α} :
    a ≤ min b c ↔ a ≤ b ∧ a ≤ c :=
  LawfulOrderInf.le_min_iff a b c

public theorem min_le_left {α : Type u} [Min α] [LE α] [Refl (α := α) (· ≤ ·)] [LawfulOrderInf α]
    {a b : α} : min a b ≤ a :=
  le_min_iff.mp (le_refl _) |>.1

public theorem min_le_right {α : Type u} [Min α] [LE α] [Refl (α := α) (· ≤ ·)] [LawfulOrderInf α]
    {a b : α} : min a b ≤ b :=
  le_min_iff.mp (le_refl _) |>.2

public theorem min_le {α : Type u} [Min α] [LE α] [IsPreorder α] [LawfulOrderMin α] {a b c : α} :
    min a b ≤ c ↔ a ≤ c ∨ b ≤ c := by
  cases MinEqOr.min_eq_or a b <;> rename_i h
  · simpa [h] using le_trans (h ▸ min_le_right (a := a) (b := b))
  · simpa [h] using le_trans (h ▸ min_le_left (a := a) (b := b))

public theorem min_eq_or {α : Type u} [Min α] [MinEqOr α] {a b : α} :
    min a b = a ∨ min a b = b :=
  MinEqOr.min_eq_or a b

public instance {α : Type u} [LE α] [Min α] [IsLinearOrder α] [LawfulOrderInf α] :
    MinEqOr α where
  min_eq_or a b := by
    cases le_total (a := a) (b := b)
    · apply Or.inl
      apply le_antisymm
      · apply min_le_left
      · rw [le_min_iff]
        exact ⟨le_refl a, ‹_›⟩
    · apply Or.inr
      apply le_antisymm
      · apply min_le_right
      · rw [le_min_iff]
        exact ⟨‹_›, le_refl b⟩

/--
If a `Min α` instance satisfies typical properties in terms of a reflexive and antisymmetric `LE α`
instance, then the `LE α` instance represents a linear order.
-/
public theorem IsLinearOrder.of_refl_of_antisymm_of_lawfulOrderMin {α : Type u} [LE α]
    [LE α] [Min α] [Refl (α := α) (· ≤ ·)] [Antisymm (α := α) (· ≤ ·)] [LawfulOrderMin α] :
    IsLinearOrder α := by
  apply IsLinearOrder.of_le
  · infer_instance
  · constructor
    intro a b c hab hbc
    have : b = min b c := by
      apply le_antisymm
      · rw [le_min_iff]
        exact ⟨le_refl b, hbc⟩
      · apply min_le_left
    rw [this, le_min_iff] at hab
    exact hab.2
  · constructor
    intro a b
    cases min_eq_or (a := a) (b := b) <;> rename_i h
    · exact Or.inl (h ▸ min_le_right)
    · exact Or.inr (h ▸ min_le_left)

public instance {α : Type u} [Min α] [MinEqOr α] :
    Std.IdempotentOp (min : α → α → α) where
  idempotent a := by cases MinEqOr.min_eq_or a a <;> assumption

public instance {α : Type u} [LE α] [Min α] [IsLinearOrder α] [LawfulOrderMin α] :
    Std.Associative (min : α → α → α) where
  assoc a b c := by apply le_antisymm <;> simp [min_le, le_min_iff, le_refl]

public theorem min_eq_if {α : Type u} [LE α] [DecidableLE α] {_ : Min α}
    [LawfulOrderLeftLeaningMin α] {a b : α} :
    min a b = if a ≤ b then a else b := by
  split <;> rename_i h
  · simp [LawfulOrderLeftLeaningMin.min_eq_left _ _ h]
  · simp [LawfulOrderLeftLeaningMin.min_eq_right _ _ h]

public theorem max_eq_if {α : Type u} [LE α] [DecidableLE α] {_ : Max α}
    [LawfulOrderLeftLeaningMax α] {a b : α} :
    max a b = if b ≤ a then a else b := by
  split <;> rename_i h
  · simp [LawfulOrderLeftLeaningMax.max_eq_left _ _ h]
  · simp [LawfulOrderLeftLeaningMax.max_eq_right _ _ h]

public instance {α : Type u} [LE α] [Min α] [IsLinearOrder α] [LawfulOrderInf α] :
    LawfulOrderLeftLeaningMin α where
  min_eq_left a b hab := by
    apply le_antisymm
    · apply min_le_left
    · simp [le_min_iff, le_refl, hab]
  min_eq_right a b hab := by
    apply le_antisymm
    · apply min_le_right
    · simp [le_min_iff, le_refl, le_of_not_ge hab]

public theorem LawfulOrderLeftLeaningMin.of_eq {α : Type u} [LE α] [Min α] [DecidableLE α]
    (min_eq : ∀ a b : α, min a b = if a ≤ b then a else b) : LawfulOrderLeftLeaningMin α where
  min_eq_left a b := by simp +contextual [min_eq]
  min_eq_right a b := by simp +contextual [min_eq]

attribute [local instance] Min.leftLeaningOfLE
public instance [LE α] [DecidableLE α] : LawfulOrderLeftLeaningMin α :=
  .of_eq (fun a b => by simp [min])

public instance {α : Type u} [LE α] [Min α] [LawfulOrderLeftLeaningMin α] :
    MinEqOr α where
  min_eq_or a b := by
    open scoped Classical in
    suffices min_eq : min a b = if a ≤ b then a else b by
      rw [min_eq]
      split <;> simp
    split <;> simp [*, LawfulOrderLeftLeaningMin.min_eq_left, LawfulOrderLeftLeaningMin.min_eq_right]

public instance {α : Type u} [LE α] [Min α] [IsLinearPreorder α] [LawfulOrderLeftLeaningMin α] :
    LawfulOrderMin α where
  toMinEqOr := inferInstance
  le_min_iff a b c := by
    open scoped Classical in
    suffices min_eq : min b c = if b ≤ c then b else c by
      rw [min_eq]
      split <;> rename_i hbc
      · simp only [iff_self_and]
        exact fun hab => le_trans hab hbc
      · simp only [iff_and_self]
        exact fun hac => le_trans hac (by simpa [hbc] using Std.le_total (a := b) (b := c))
    split <;> simp [*, LawfulOrderLeftLeaningMin.min_eq_left, LawfulOrderLeftLeaningMin.min_eq_right]

end Min
end Std

namespace Classical.Order
open Std

public noncomputable scoped instance instMin {α : Type u} [LE α] : Min α :=
  .leftLeaningOfLE α

end Classical.Order

namespace Std
section Max

public theorem max_self {α : Type u} [Max α] [Std.IdempotentOp (max : α → α → α)] {a : α} :
    max a a = a :=
  Std.IdempotentOp.idempotent a

public theorem max_le_iff {α : Type u} [Max α] [LE α] [LawfulOrderSup α] {a b c : α} :
    max a b ≤ c ↔ a ≤ c ∧ b ≤ c :=
  LawfulOrderSup.max_le_iff a b c

public theorem left_le_max {α : Type u} [Max α] [LE α] [Refl (α := α) (· ≤ ·)] [LawfulOrderSup α]
    {a b : α} : a ≤ max a b :=
  max_le_iff.mp (le_refl _) |>.1

public theorem right_le_max {α : Type u} [Max α] [LE α] [Refl (α := α) (· ≤ ·)]
    [LawfulOrderSup α] {a b : α} : b ≤ max a b :=
  max_le_iff.mp (le_refl _) |>.2

public theorem le_max {α : Type u} [Max α] [LE α] [IsPreorder α] [LawfulOrderMax α] {a b c : α} :
    a ≤ max b c ↔ a ≤ b ∨ a ≤ c := by
  cases MaxEqOr.max_eq_or b c <;> rename_i h
  · simpa [h] using (le_trans · (h ▸ right_le_max))
  · simpa [h] using (le_trans · (h ▸ left_le_max))

public theorem max_eq_or {α : Type u} [Max α] [MaxEqOr α] {a b : α} :
    max a b = a ∨ max a b = b :=
  MaxEqOr.max_eq_or a b

public instance {α : Type u} [LE α] [Max α] [IsLinearOrder α] [LawfulOrderSup α] :
    MaxEqOr α where
  max_eq_or a b := by
    cases le_total (a := a) (b := b)
    · apply Or.inr
      apply le_antisymm
      · rw [max_le_iff]
        exact ⟨‹_›, le_refl b⟩
      · apply right_le_max
    · apply Or.inl
      apply le_antisymm
      · rw [max_le_iff]
        exact ⟨le_refl a, ‹_›⟩
      · apply left_le_max

/--
If a `Max α` instance satisfies typical properties in terms of a reflexive and antisymmetric `LE α`
instance, then the `LE α` instance represents a linear order.
-/
public theorem IsLinearOrder.of_refl_of_antisymm_of_lawfulOrderMax {α : Type u} [LE α] [Max α]
    [Refl (α := α) (· ≤ ·)] [Antisymm (α := α) (· ≤ ·)] [LawfulOrderMax α] :
    IsLinearOrder α := by
  apply IsLinearOrder.of_le
  · infer_instance
  · constructor
    intro a b c hab hbc
    have : b = max a b := by
      apply le_antisymm
      · exact right_le_max
      · rw [max_le_iff]
        exact ⟨hab, le_refl b⟩
    rw [this, max_le_iff] at hbc
    exact hbc.1
  · constructor
    intro a b
    cases max_eq_or (a := a) (b := b) <;> rename_i h
    · exact Or.inr (h ▸ right_le_max)
    · exact Or.inl (h ▸ left_le_max)

public instance {α : Type u} [Max α] [MaxEqOr α] {P : α → Prop} : Max (Subtype P) where
  max a b := ⟨Max.max a.val b.val, MaxEqOr.elim a.property b.property⟩

public instance {α : Type u} [Max α] [MaxEqOr α] :
    Std.IdempotentOp (max : α → α → α) where
  idempotent a := by cases MaxEqOr.max_eq_or a a <;> assumption

public instance {α : Type u} [LE α] [Max α] [IsLinearOrder α] [LawfulOrderMax α] :
    Std.Associative (max : α → α → α) where
  assoc a b c := by
    apply le_antisymm
    all_goals
      simp only [max_le_iff]
      simp [le_max, le_refl]

public instance {α : Type u} [LE α] [Max α] [IsLinearOrder α] [LawfulOrderSup α] :
    LawfulOrderLeftLeaningMax α where
  max_eq_left a b hab := by
    apply le_antisymm
    · simp [max_le_iff, le_refl, hab]
    · apply left_le_max
  max_eq_right a b hab := by
    apply le_antisymm
    · simp [max_le_iff, le_refl, le_of_not_ge hab]
    · apply right_le_max

public theorem LawfulOrderLeftLeaningMax.of_eq {α : Type u} [LE α] [Max α] [DecidableLE α]
    (min_eq : ∀ a b : α, max a b = if b ≤ a then a else b) : LawfulOrderLeftLeaningMax α where
  max_eq_left a b := by simp +contextual [min_eq]
  max_eq_right a b := by simp +contextual [min_eq]

attribute [local instance] Max.leftLeaningOfLE
public instance [LE α] [DecidableLE α] : LawfulOrderLeftLeaningMax α :=
  .of_eq (fun a b => by simp [max])

public instance {α : Type u} [LE α] [Max α] [LawfulOrderLeftLeaningMax α] :
    MaxEqOr α where
  max_eq_or a b := by
    open scoped Classical in
    suffices min_eq : max a b = if b ≤ a then a else b by
      rw [min_eq]
      split <;> simp
    split <;> simp [*, LawfulOrderLeftLeaningMax.max_eq_left, LawfulOrderLeftLeaningMax.max_eq_right]

public instance {α : Type u} [LE α] [Max α] [IsLinearPreorder α] [LawfulOrderLeftLeaningMax α] :
    LawfulOrderMax α where
  toMaxEqOr := inferInstance
  max_le_iff a b c := by
    open scoped Classical in
    suffices max_eq : max a b = if b ≤ a then a else b by
      rw [max_eq]
      split <;> rename_i hba
      · simp only [iff_self_and]
        exact fun hac => le_trans hba hac
      · simp only [iff_and_self]
        exact fun hbc => le_trans (by simpa [hba] using Std.le_total (a := b) (b := a)) hbc
    split <;> simp [*, LawfulOrderLeftLeaningMax.max_eq_left, LawfulOrderLeftLeaningMax.max_eq_right]

end Max
end Std

namespace Classical.Order
open Std

public noncomputable scoped instance instMax {α : Type u} [LE α] : Max α :=
  .leftLeaningOfLE α

end Classical.Order
