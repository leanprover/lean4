module

prelude
public import Init.Core
public import Std.Classes.Ord.Basic
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
class PartiallyComparable (α : Type u) where
  compare : α → α → PartialOrdering

def PartiallyComparable.ofCmp {α : Type u} (cmp : α → α → Ordering) : PartiallyComparable α where
  compare a b := some (cmp a b)

abbrev PartiallyComparable.ofOrd (α : Type u) [Ord α] : PartiallyComparable α :=
  .ofCmp Ord.compare

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

class LawfulPartiallyComparableCmp {α : Type u} (c : PartiallyComparable α) (cmp : α → α → Ordering) where
  compare_eq_some_compare : ∀ a b, c.compare a b = some (cmp a b)

abbrev LawfulPartiallyComparableOrd {α : Type u} [Ord α] (c : PartiallyComparable α) :=
  LawfulPartiallyComparableCmp c compare

class LawfulPartiallyComparableBEq {α : Type u} [BEq α] (c : PartiallyComparable α) where
  beq_iff_compare_eq_some_eq : ∀ a b : α, a == b ↔ c.compare a b = some .eq

class LawfulTotallyComparable {α : Type u} (c : PartiallyComparable α) where
  isSome_compare : ∀ a b, (c.compare a b).isSome

class LawfulPreorder {α : Type u} (pc : PartiallyComparable α) where
  le_trans : ∀ a b c : α, (pc.compare a b).isLE → (pc.compare b c).isLE → (pc.compare a c).isLE
  le_refl : ∀ a : α, pc.compare a a = some .eq
  gt_iff_lt : ∀ a b : α, pc.compare a b = some .gt ↔ pc.compare b a = some .lt

class LawfulLinearPreorder {α : Type u} (pc : PartiallyComparable α) extends
    LawfulPreorder pc, LawfulTotallyComparable pc

instance (α : Type u) [Ord α] [LawfulLinearPreorder (.ofOrd α)] : Std.TransOrd α :=
  sorry

instance (α : Type u) [BEq α] [Ord α] [LawfulLinearPreorder (.ofOrd α)]
    [LawfulPartiallyComparableBEq (.ofOrd α)] : EquivBEq α :=
  sorry

instance (α : Type u) [BEq α] [Ord α] [LawfulPartiallyComparableBEq (.ofOrd α)] :
    Std.LawfulBEqOrd α :=
  sorry

instance (α : Type u) {_ : Ord α} [LawfulLinearPreorder (.ofOrd α)] :
    haveI : Ord α := Ord.opposite inferInstance; LawfulLinearPreorder (.ofOrd α) :=
  sorry

class LawfulPartialOrder {α : Type u} (pc : PartiallyComparable α) extends LawfulPreorder pc where
  le_antisymm : ∀ a b : α, pc.compare a b = some .eq → a = b

class LawfulLinearOrder {α : Type u} (pc : PartiallyComparable α) extends
    LawfulPartialOrder pc, LawfulLinearPreorder pc

theorem LawfulPartiallyComparableCmp.eq_ofCmp {α : Type u} {cmp : α → α → Ordering} {c : PartiallyComparable α}
    [i : LawfulPartiallyComparableCmp c cmp] :
    c = .ofCmp cmp := by
  ext a b
  simp [PartiallyComparable.ofCmp, i.compare_eq_some_compare a b]

theorem LawfulPartiallyComparableOrd.eq_ofOrd {α : Type u} [Ord α] {c : PartiallyComparable α}
    [i : LawfulPartiallyComparableOrd c] :
    c = .ofOrd α := by
  simp [LawfulPartiallyComparableCmp.eq_ofCmp (cmp := compare)]

instance (α : Type u) (cmp : α → α → Ordering) : LawfulPartiallyComparableCmp (.ofCmp cmp) cmp where
  compare_eq_some_compare := fun _ _ => by rfl

instance (α : Type u) [Ord α] : LawfulTotallyComparable (.ofOrd α) where
  isSome_compare := by simp [PartiallyComparable.ofOrd, PartiallyComparable.ofCmp]

instance (α : Type u) (cmp : α → α → Ordering) [LawfulPartialOrder (.ofCmp cmp)] :
    Std.LawfulEqCmp cmp where
  compare_self := by
    intro a
    have := LawfulPreorder.le_refl (pc := .ofCmp cmp) a
    simpa [LawfulPartiallyComparableCmp.compare_eq_some_compare (cmp := cmp)] using this
  eq_of_compare := by
    intro a b
    have := LawfulPartialOrder.le_antisymm (pc := .ofCmp cmp) a b
    simpa [LawfulPartiallyComparableCmp.compare_eq_some_compare (cmp := cmp)] using this

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

instance {α : Type u} [LT α] : LawfulTotallyComparable (.ofLT α) where
  isSome_compare a b := by
    simp only [PartiallyComparable.ofLT]
    split
    · simp
    · split <;> simp

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

instance [LE α] (cmp : α → α → Ordering) [i : LawfulPartiallyComparableCmp (.ofLE α) cmp]
    [OrderProp P (.ofLE α)] : OrderProp P (.ofCmp cmp) := by
  rw [← i.eq_ofCmp]; infer_instance

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

theorem lt_iff_le_and_not_ge [LE α] [LT α] [i : LawfulOrientedPartiallyComparableLT (.ofLE α)]
    {a b : α} : a < b ↔ a ≤ b ∧ ¬ b ≤ a := by
  simp [i.lt_iff_compare_eq_some_lt, PartiallyComparable.ofLE]
  split <;> split <;> simp_all

-- Demo: an alternative formulation of the lemma in terms of LT
-- Note that this is more restrictive because `ofLT` is total by construction.
example [LE α] [LT α] [LawfulOrientedPartiallyComparableLE (.ofLT α)]
    [Std.Asymm (α := α) (· < ·)]
    {a b : α} : a < b ↔ a ≤ b ∧ ¬ b ≤ a := by
  -- base change works!
  apply lt_iff_le_and_not_ge

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
  sorry
