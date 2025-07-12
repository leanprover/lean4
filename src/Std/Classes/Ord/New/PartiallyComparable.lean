module

prelude
public import Init.Core
public import Std.Classes.Ord.New.BasicOperations

public section

abbrev PartialOrdering := Option Ordering

def PartialOrdering.isLE : PartialOrdering → Bool
  | none => false
  | some o => o.isLE

def PartialOrdering.isGE : PartialOrdering → Bool
  | none => false
  | some o => o.isGE

@[ext]
structure PartiallyComparable (α : Type u) where
  compare : α → α → PartialOrdering

def PartiallyComparable.ofOrd (α : Type u) [Ord α] : PartiallyComparable α where
  compare a b := some (Ord.compare a b)

open Classical in
noncomputable def PartiallyComparable.ofLE (α : Type u) [LE α] : PartiallyComparable α where
  compare a b :=
    if a ≤ b then
      if b ≤ a then some .eq else some .lt
    else
      if b ≤ a then some .gt else none

open Classical in
noncomputable def PartiallyComparable.ofLT (α : Type u) [LT α] : PartiallyComparable α where
  compare a b := if a < b then some .lt else if b < a then some .gt else some .eq

class LawfulOrientedPartiallyComparableLE {α : Type u} [LE α] (c : PartiallyComparable α) where
  le_iff_compare_isLE : ∀ a b : α, a ≤ b ↔ (c.compare a b).isLE
  ge_iff_compare_isGE : ∀ a b : α, b ≤ a ↔ (c.compare a b).isGE

class LawfulOrientedPartiallyComparableLT {α : Type u} [LT α] (c : PartiallyComparable α) where
  lt_iff_compare_eq_some_lt : ∀ a b : α, a < b ↔ c.compare a b = some .lt
  gt_iff_compare_eq_some_gt : ∀ a b : α, b < a ↔ c.compare a b = some .gt

class LawfulPartiallyComparableOrd {α : Type u} [Ord α] (c : PartiallyComparable α) where
  compare_eq_some_compare : ∀ a b, c.compare a b = some (compare a b)

class LawfulTotallyComparable {α : Type u} (c : PartiallyComparable α) where
  isSome_compare : ∀ a b, (c.compare a b).isSome

-- not really useful, I think
class PartiallyComparableEq {α : Type u} (c d : PartiallyComparable α) where
  eq : c = d

instance {α : Type u} {c d : PartiallyComparable α} [PartiallyComparableEq c d] :
    PartiallyComparableEq d c where
  eq := PartiallyComparableEq.eq.symm

theorem LawfulPartiallyComparableOrd.eq_ofOrd {α : Type u} [Ord α] {c : PartiallyComparable α}
    [i : LawfulPartiallyComparableOrd c] :
    c = .ofOrd α := by
  ext a b
  simp [PartiallyComparable.ofOrd, i.compare_eq_some_compare a b]

instance {α : Type u} [Ord α] {c : PartiallyComparable α} [LawfulPartiallyComparableOrd c] :
    PartiallyComparableEq c (.ofOrd α) where
  eq := LawfulPartiallyComparableOrd.eq_ofOrd

instance (α : Type u) [Ord α] : LawfulPartiallyComparableOrd (.ofOrd α) where
  compare_eq_some_compare := fun _ _ => by rfl

instance (α : Type u) [Ord α] : LawfulTotallyComparable (.ofOrd α) where
  isSome_compare := by simp [PartiallyComparable.ofOrd]

theorem LawfulOrientedPartiallyComparableLE.eq_ofLE {α : Type u} [LE α] {c : PartiallyComparable α}
    [i : LawfulOrientedPartiallyComparableLE c] :
    c = .ofLE α := by
  ext a b
  have hle := i.le_iff_compare_isLE a b
  have hge := i.ge_iff_compare_isGE a b
  simp only [PartiallyComparable.ofLE, hle, hge]
  cases c.compare a b
  · simp [PartialOrdering.isLE, PartialOrdering.isGE]
  · rename_i o
    simp only [PartialOrdering.isLE, PartialOrdering.isGE]
    cases o <;> simp

instance {α : Type u} [LE α] {c : PartiallyComparable α} [LawfulOrientedPartiallyComparableLE c] :
    PartiallyComparableEq c (.ofLE α) where
  eq := LawfulOrientedPartiallyComparableLE.eq_ofLE

instance (α : Type u) [LE α] : LawfulOrientedPartiallyComparableLE (.ofLE α) where
  le_iff_compare_isLE a b := by
    simp only [PartiallyComparable.ofLE]
    split <;> split <;> simp_all [PartialOrdering.isLE]
  ge_iff_compare_isGE a b := by
    simp only [PartiallyComparable.ofLE]
    split <;> split <;> simp_all [PartialOrdering.isGE]

theorem LawfulOrientedPartiallyComparableLT.eq_ofLT {α : Type u} [LT α] {c : PartiallyComparable α}
    [i : LawfulOrientedPartiallyComparableLT c] [LawfulTotallyComparable c] :
    c = .ofLT α := by
  ext a b
  have hlt := i.lt_iff_compare_eq_some_lt a b
  have hgt := i.gt_iff_compare_eq_some_gt a b
  simp [PartiallyComparable.ofLT, hlt, hgt]
  cases h : c.compare a b
  · have := LawfulTotallyComparable.isSome_compare (c := c) a b
    simp [h] at this
  · rename_i o
    cases o <;> simp_all

instance {α : Type u} [LT α] {c : PartiallyComparable α} [LawfulOrientedPartiallyComparableLT c]
    [LawfulTotallyComparable c] :
    PartiallyComparableEq c (.ofLT α) where
  eq := LawfulOrientedPartiallyComparableLT.eq_ofLT

instance (α : Type u) [LT α] [Std.Asymm (α := α) (· < ·)] :
    LawfulOrientedPartiallyComparableLT (.ofLT α) where
  lt_iff_compare_eq_some_lt a b := by
    simp [PartiallyComparable.ofLT]
    constructor
    · intro h
      simp [h]
    · intro h
      split at h <;> simp_all
  gt_iff_compare_eq_some_gt a b := by
    simp [PartiallyComparable.ofLT]
    split
    · simp
      apply Std.Asymm.asymm
      assumption
    · simp

section OrderProp

class OrderProp {α : Type u} (P : PartiallyComparable α → Prop) (c : PartiallyComparable α) where
  inner : P c

variable {α : Type u} {P : PartiallyComparable α → Prop}

instance [Ord α] [LE α] [i : LawfulOrientedPartiallyComparableLE (.ofOrd α)]
    [OrderProp P (.ofOrd α)] : OrderProp P (.ofLE α) := by
  rw [← i.eq_ofLE]; infer_instance

instance [Ord α] [LT α] [i : LawfulOrientedPartiallyComparableLT (.ofOrd α)]
    [LawfulTotallyComparable (.ofOrd α)] [OrderProp P (.ofOrd α)] : OrderProp P (.ofLT α) := by
  rw [← i.eq_ofLT]; infer_instance

instance [LE α] [Ord α] [i : LawfulPartiallyComparableOrd (.ofLE α)]
    [OrderProp P (.ofLE α)] : OrderProp P (.ofOrd α) := by
  rw [← i.eq_ofOrd]; infer_instance

instance [LE α] [LT α] [i : LawfulOrientedPartiallyComparableLT (.ofLE α)]
    [LawfulTotallyComparable (.ofLE α)] [OrderProp P (.ofLE α)] : OrderProp P (.ofLT α) := by
  rw [← i.eq_ofLT]; infer_instance

instance [LT α] [Ord α] [i : LawfulPartiallyComparableOrd (.ofLT α)] [Std.Asymm (α := α) (· < ·)]
    [OrderProp P (.ofLT α)] : OrderProp P (.ofOrd α) := by
  rw [← i.eq_ofOrd]; infer_instance

instance [LT α] [LE α] [i : LawfulOrientedPartiallyComparableLE (.ofLT α)] [Std.Asymm (α := α) (· < ·)]
    [OrderProp P (.ofLT α)] : OrderProp P (.ofLE α) := by
  rw [← i.eq_ofLE]; infer_instance

end OrderProp

instance (α : Type u) (c : PartiallyComparable α) [Ord α] [LawfulPartiallyComparableOrd c] :
    OrderProp LawfulPartiallyComparableOrd c where
  inner := inferInstance

instance (α : Type u) (c : PartiallyComparable α) [Ord α] [OrderProp LawfulPartiallyComparableOrd c] :
    LawfulPartiallyComparableOrd c :=
  OrderProp.inner

instance (α : Type u) (c : PartiallyComparable α) [LE α] [LawfulOrientedPartiallyComparableLE c] :
    OrderProp LawfulOrientedPartiallyComparableLE c where
  inner := inferInstance

instance (α : Type u) (c : PartiallyComparable α) [LE α]
    [OrderProp LawfulOrientedPartiallyComparableLE c] : LawfulOrientedPartiallyComparableLE c :=
  OrderProp.inner

instance (α : Type u) (c : PartiallyComparable α) [LT α] [LawfulOrientedPartiallyComparableLT c] :
    OrderProp LawfulOrientedPartiallyComparableLT c where
  inner := inferInstance

instance (α : Type u) (c : PartiallyComparable α) [LT α]
    [OrderProp LawfulOrientedPartiallyComparableLT c] : LawfulOrientedPartiallyComparableLT c :=
  OrderProp.inner

instance (α : Type u) (c : PartiallyComparable α) [LawfulTotallyComparable c] :
    OrderProp LawfulTotallyComparable c where
  inner := inferInstance

instance (α : Type u) (c : PartiallyComparable α) [OrderProp LawfulTotallyComparable c] :
    LawfulTotallyComparable c :=
  OrderProp.inner

theorem le_total [LE α] [i : LawfulTotallyComparable (.ofLE α)] {a b : α} :
    a ≤ b ∨ b ≤ a := by
  have := i.isSome_compare a b
  simp only [PartiallyComparable.ofLE] at this
  split at this
  · exact Or.inl ‹_›
  · split at this
    · exact Or.inr ‹_›
    · cases this

example [LE α] [Ord α]
    [i : LawfulOrientedPartiallyComparableLE (.ofOrd α)] {a b : α} :
    (compare a b).isLE ∨ (compare a b).isGE := by
  -- The required LawfulTotallyComparable (.ofLE α) instance is inferred as expected
  have := le_total (α := α) (a := a) (b := b)
  -- Sad: I need to explicitly reference the instance I want.
  simp [i.le_iff_compare_isLE] at this


-- -- Ord: ofOrd -> ofLE
-- instance (α : Type u) [Ord α] [LE α] [i : LawfulOrientedPartiallyComparableLE (.ofOrd α)] :
--     LawfulPartiallyComparableOrd (.ofLE α) := by
--   rw [i.eq_ofLE.symm]
--   infer_instance

-- -- LE: ofOrd -> ofLE unnecessary

-- -- LT: ofOrd -> ofLE
-- instance (α : Type u) [Ord α] [LE α] [LT α] [i : LawfulOrientedPartiallyComparableLE (.ofOrd α)]
--     [LawfulOrientedPartiallyComparableLT (.ofLE α)] :
--     LawfulOrientedPartiallyComparableLE (.ofLE α) := by
--   rw [i.eq_ofLE.symm]
--   infer_instance


-- -- Ord: ofOrd -> ofLT
-- instance {α : Type u} [Ord α] [LT α] [i : LawfulOrientedPartiallyComparableLT (.ofOrd α)]
--     [LawfulTotallyComparable (.ofOrd α)] :
--     LawfulPartiallyComparableOrd (.ofLT α) := by
--   rw [i.eq_ofLT.symm]
--   infer_instance

-- -- LE: ofOrd -> ofLT
-- instance {α : Type u} [Ord α] [LT α] [LE α] [i : LawfulOrientedPartiallyComparableLT (.ofOrd α)]
--     [LawfulOrientedPartiallyComparableLE (.ofOrd α)]
--     [LawfulTotallyComparable (.ofOrd α)] :
--     LawfulOrientedPartiallyComparableLE (.ofLT α) := by
--   rw [i.eq_ofLT.symm]
--   infer_instance

-- -- LT: ofOrd -> ofLT
-- instance {α : Type u} [Ord α] [LT α] [i : LawfulOrientedPartiallyComparableLT (.ofOrd α)]
--     [LawfulTotallyComparable (.ofOrd α)] :
--     LawfulOrientedPartiallyComparableLT (.ofLT α) := by
--   rw [i.eq_ofLT.symm]
--   infer_instance


-- -- Ord: ofLE -> ofOrd unnecessary

-- -- LE: ofLE -> ofOrd
-- instance (α : Type u) [Ord α] [LE α] [i : LawfulPartiallyComparableOrd (.ofLE α)] :
--     LawfulOrientedPartiallyComparableLE (.ofOrd α) := by
--   rw [i.eq_ofOrd.symm]
--   infer_instance

-- -- LT: ofLE -> ofOrd
-- instance (α : Type u) [Ord α] [LE α] [LT α] [Std.Asymm (α := α) (· < ·)]
--     [i : LawfulPartiallyComparableOrd (.ofLE α)]
--     [LawfulOrientedPartiallyComparableLT (.ofLE α)] :
--     LawfulOrientedPartiallyComparableLT (.ofOrd α) := by
--   rw [i.eq_ofOrd.symm]
--   infer_instance


-- -- Ord: ofLE -> ofLT
-- instance (α : Type u) [Ord α] [LE α] [LT α] [i : LawfulOrientedPartiallyComparableLT (.ofLE α)]
--     [LawfulPartiallyComparableOrd (.ofLE α)] [LawfulTotallyComparable (.ofLE α)] :
--     LawfulOrientedPartiallyComparableLT (.ofLT α) := by
--   rw [i.eq_ofLT.symm]
--   infer_instance

-- -- LE: ofLE -> ofLT
-- instance (α : Type u) [LE α] [LT α] [i : LawfulOrientedPartiallyComparableLT (.ofLE α)]
--     [LawfulTotallyComparable (.ofLE α)] :
--     LawfulOrientedPartiallyComparableLE (.ofLT α) := by
--   rw [i.eq_ofLT.symm]
--   infer_instance

-- -- LT: ofLE -> ofLT unnecessary


-- -- Ord: ofLT -> ofOrd unnecessary

-- -- LE: ofLT -> ofOrd
-- instance (α : Type u) [Ord α] [LT α] [LE α] [Std.Asymm (α := α) (· < ·)]
--     [i : LawfulPartiallyComparableOrd (.ofLT α)] [LawfulOrientedPartiallyComparableLE (.ofLT α)] :
--     LawfulOrientedPartiallyComparableLT (.ofOrd α) := by
--   rw [i.eq_ofOrd.symm]
--   infer_instance

-- -- LT: ofLT -> ofOrd
-- instance (α : Type u) [Ord α] [LT α] [Std.Asymm (α := α) (· < ·)]
--     [i : LawfulPartiallyComparableOrd (.ofLT α)] :
--     LawfulOrientedPartiallyComparableLT (.ofOrd α) := by
--   rw [i.eq_ofOrd.symm]
--   infer_instance


-- -- Ord: ofLT -> ofLE
-- instance (α : Type u) [Ord α] [LT α] [LE α] [Std.Asymm (α := α) (· < ·)]
--     [i : LawfulOrientedPartiallyComparableLE (.ofLT α)] [LawfulPartiallyComparableOrd (.ofLT α)] :
--     LawfulPartiallyComparableOrd (.ofLE α) := by
--   rw [i.eq_ofLE.symm]
--   infer_instance

-- -- LE: ofLT -> ofLE unnecessary

-- -- LT: ofLT -> ofLE
-- instance (α : Type u) [LT α] [LE α] [Std.Asymm (α := α) (· < ·)]
--     [i : LawfulOrientedPartiallyComparableLE (.ofLT α)] :
--     LawfulOrientedPartiallyComparableLT (.ofLE α) := by
--   rw [i.eq_ofLE.symm]
--   infer_instance


-- TODO: LawfulTotallyComparable: ofOrd -> ofLE etc.
-- Perhaps create a mechanism that makes it less tedious to add more such properties
