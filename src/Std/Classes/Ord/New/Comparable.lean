module

prelude
public import Init.Core
public import Std.Classes.Ord.Basic
public import Std.Classes.Ord.New.PartiallyComparable

public section

class Comparable (α : Type u) extends PartiallyComparable α, NoncomputableOrd α

def Comparable.GT {α : Type u} [Comparable α] (a b : α) : Prop :=
  open Classical.Order in
  compare a b = .gt

class ComputablyComparable (α : Type u) extends Comparable α, ComputablyPartiallyComparable α, Ord α

-- TODO: This is already oriented!
class LawfulComparable (α : Type u) [Comparable α] extends
    LawfulPartiallyComparable α where
  eq_lt_iff_lt : ∀ a b : α, NoncomputableOrd.compare a b = .lt ↔ LT.lt a b := by exact Iff.rfl
  isLE_iff_le : ∀ a b : α, (NoncomputableOrd.compare a b).isLE ↔ LE.le a b := by exact Iff.rfl

class LawfulOrientedComparable (α : Type u) [Comparable α] extends LawfulComparable α where
  eq_gt_iff_gt : ∀ (a b : α), NoncomputableOrd.compare a b = .gt ↔ LT.lt b a := by exact Iff.rfl

theorem Comparable.compare_eq_lt_iff_lt {α : Type u} [Ord α] [Comparable α]
    [LawfulComparable α] [LawfulOrd α] : ∀ {a b : α}, compare a b = .lt ↔ a < b := by
  intro a b
  simp [← LawfulOrd.compare_eq_compare, LawfulComparable.eq_lt_iff_lt]

theorem Comparable.compare_eq_gt_iff_gt {α : Type u} [Ord α] [Comparable α]
    [LawfulOrientedComparable α] [LawfulOrd α] : ∀ {a b : α}, compare a b = .gt ↔ b < a := by
  intro a b
  simp [← LawfulOrd.compare_eq_compare, LawfulOrientedComparable.eq_gt_iff_gt]

theorem Comparable.compare_isLE {α : Type u} [Ord α] [Comparable α] [LawfulOrd α] [LawfulComparable α]
    {a b : α} : (compare a b).isLE ↔ a ≤ b := by
  simp [← LawfulOrd.compare_eq_compare, LawfulComparable.isLE_iff_le]

theorem Comparable.compare_eq_gt {α : Type u} [Ord α] [Comparable α]
    [LawfulOrientedComparable α] [LawfulOrd α] {a b : α} :
    compare a b = .gt ↔ compare b a = .lt := by
  simp [← LawfulOrd.compare_eq_compare, LawfulOrientedComparable.eq_gt_iff_gt,
    LawfulComparable.eq_lt_iff_lt]

instance (α : Type u) [Ord α] [Comparable α] [LawfulOrd α] [LawfulOrientedComparable α] :
    Std.OrientedOrd α where
  eq_swap := by
    intro a b
    cases h : compare b a
    · simp [Comparable.compare_eq_gt, h]
    · simp only [Ordering.swap_eq]
      cases h' : compare a b
      · simp_all [← Comparable.compare_eq_gt]
      · rfl
      · simp_all [Comparable.compare_eq_gt]
    · simp [← Comparable.compare_eq_gt, h]

instance (α : Type u) [BEq α] [Ord α] [Comparable α] [LawfulComputableBEq α] [LawfulOrd α]
    [LawfulOrientedComparable α] :
    Std.LawfulBEqOrd α where
  compare_eq_iff_beq {a b} := by
    cases h : compare a b
    all_goals simp [PartiallyComparable.beq_iff_le_ge, ← LawfulComparable.isLE_iff_le,
      LawfulOrd.compare_eq_compare, Std.OrientedOrd.eq_swap (a := b), h]

@[expose]
def Comparable.leOfNoncomputableOrd (α : Type u) [NoncomputableOrd α] : LE α where
  le a b := (NoncomputableOrd.compare a b).isLE

@[expose]
def Comparable.ltOfNoncomputableOrd (α : Type u) [NoncomputableOrd α] : LT α where
  lt a b := (NoncomputableOrd.compare a b).isLT

@[expose]
def Comparable.noncomputableBEqOfNoncomputableOrd (α : Type u) [NoncomputableOrd α] :
    NoncomputableBEq α :=
  .ofRel fun a b => NoncomputableOrd.compare a b = .eq

structure Comparable.OfNoncomputableOrdArgs (α : Type u) where
  instNoncomputableOrd : NoncomputableOrd α := by
    try (infer_instance; done)
    all_goals (exact NoncomputableOrd.ofComputable; done)
  instLE : LE α := by
    try (infer_instance; done)
    try (exact LE.ofBLE; done)
    all_goals (exact Comparable.leOfNoncomputableOrd _; done)
  instLT : LT α := by
    try (infer_instance; done)
    try (exact LT.ofBLT; done)
    all_goals (exact Comparable.ltOfNoncomputableOrd _; done)
  instNoncomputableBEq : NoncomputableBEq α := by
    try (infer_instance; done)
    try (exact NoncomputableBEq.ofComputable; done)
    all_goals (exact Comparable.noncomputableBEqOfNoncomputableOrd _; done)

def Comparable.ofNoncomputableOrd {α : Type u} (args : OfNoncomputableOrdArgs α) : Comparable α where
  toNoncomputableOrd := args.instNoncomputableOrd
  toLE := args.instLE
  toLT := args.instLT
  toNoncomputableBEq := args.instNoncomputableBEq

@[expose]
def Comparable.bleOfOrd (α : Type u) [Ord α] : BLE α where
  LE a b := (compare a b).isLE

@[expose]
def Comparable.leOfOrd (α : Type u) [Ord α] : LE α where
  le a b := (compare a b).isLE

@[expose]
def Comparable.bltOfOrd (α : Type u) [Ord α] : BLT α where
  LT a b := (compare a b).isLT

@[expose]
def Comparable.ltOfOrd (α : Type u) [Ord α] : LT α where
  lt a b := (compare a b).isLT

@[expose]
def Comparable.beqOfOrd (α : Type u) [Ord α] :
    BEq α :=
  ⟨fun a b => compare a b = .eq⟩

@[expose]
def Comparable.noncomputableBEqOfOrd (α : Type u) [Ord α] :
    NoncomputableBEq α :=
  .ofRel fun a b => compare a b = .eq

structure ComputablyComparable.OfOrdArgs (α : Type u) where
  instOrd : Ord α := by
    all_goals (infer_instance; done)
  instNoncomputableOrd : NoncomputableOrd α := by
    try (infer_instance; done)
    all_goals (exact NoncomputableOrd.ofComputable; done)
  instBLE : BLE α := by
    try (infer_instance; done)
    all_goals (exact Comparable.bleOfOrd _; done)
  instLE : LE α := by
    try (infer_instance; done)
    all_goals (exact Comparable.leOfOrd _; done)
  instBLT : BLT α := by
    try (infer_instance; done)
    all_goals (exact Comparable.bltOfOrd _; done)
  instLT : LT α := by
    try (infer_instance; done)
    all_goals (exact Comparable.ltOfOrd _; done)
  instBEq : BEq α := by
    try (infer_instance; done)
    all_goals (exact Comparable.beqOfOrd _; done)
  instNoncomputableBEq : NoncomputableBEq α := by
    try (infer_instance; done)
    all_goals (exact Comparable.noncomputableBEqOfOrd _; done)

abbrev ComputablyComparable.ofOrd {α : Type u} (args : OfOrdArgs α) : ComputablyComparable α where
  toOrd := args.instOrd
  toNoncomputableOrd := args.instNoncomputableOrd
  toBLE := args.instBLE
  toLE := args.instLE
  toBLT := args.instBLT
  toLT := args.instLT
  toBEq := args.instBEq
  toNoncomputableBEq := args.instNoncomputableBEq

abbrev Comparable.ofOrd (α : Type u) [Ord α] : Comparable α :=
  ComputablyComparable.ofOrd {} |>.toComparable

instance (α : Type u) [Ord α] :
    haveI : BLE α := Comparable.bleOfOrd α
    haveI : LE α := Comparable.leOfOrd α
    LawfulBLE α :=
  letI : BLE α := Comparable.bleOfOrd α
  letI : LE α := Comparable.leOfOrd α
  ⟨by simp [Comparable.bleOfOrd, Comparable.leOfOrd]⟩

instance (α : Type u) [Ord α] :
    haveI : BLT α := Comparable.bltOfOrd α
    haveI : LT α := Comparable.ltOfOrd α
    LawfulBLT α :=
  letI : BLT α := Comparable.bltOfOrd α
  letI : LT α := Comparable.ltOfOrd α
  ⟨by simp [Comparable.bltOfOrd, Comparable.ltOfOrd]⟩

def Comparable.lawful (alpha : Type u) [NoncomputableOrd alpha]
    (oriented : ∀ a b : alpha, NoncomputableOrd.compare a b = .lt → NoncomputableOrd.compare b a = .lt) :
    haveI : Comparable alpha := .ofNoncomputableOrd {}
    LawfulComparable alpha :=
  letI : Comparable alpha := .ofNoncomputableOrd {}
  haveI : LawfulPartiallyComparable alpha := sorry
  ⟨sorry, sorry⟩

def ComputablyComparable.lawful (α : Type u) [Ord α]
    (oriented : ∀ a b : α, compare a b = .lt → compare b a = .lt) :
    haveI : ComputablyComparable α := .ofOrd {}
    LawfulComparable α :=
  letI : ComputablyComparable α := .ofOrd {}
  haveI : LawfulPartiallyComparable α := sorry
  ⟨sorry, sorry⟩

-- Cmp conundrum
-- Cmp induces Comparable, but only up to propositional equality
-- At the moment, Ord -> cmp -> Ord is definitionally equal to id
-- It would be weird and potentially inefficient to pass around a whole
--   `Comparable` instance (or worse) as an explicit argument
-- `ToComparable α β`: `β` can be converted into a `Comparable` instance?
--   For example, `ComparisonFn α` might just contain a compare function
--   But there might also simply be a `InferredComparableInstance α [Comparable α]`
--   type, which is a subsingleton.
-- Instead of `OrientedCmp cmp`, perhaps use `OrientedComparable α (i := .ofFn cmp)`?
