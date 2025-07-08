module

prelude
public import Init.Core
public import Std.Classes.Ord.New.PartiallyComparable

public section

class ComparableMixin (α : Type u) [LE α] [LT α] [NoncomputableBEq α] [NoncomputableOrd α] extends
    PartiallyComparableMixin α

class Comparable (α : Type u) extends PartiallyComparable α, NoncomputableOrd α, ComparableMixin α

class ComputablyComparable (α : Type u) extends Comparable α, ComputablyPartiallyComparable α, Ord α

class LawfulComparable (α : Type u) [LT α] [LE α] [NoncomputableBEq α] [NoncomputableOrd α] extends
    LawfulPartiallyComparable α where
  eq_lt_iff_lt : ∀ (a b : α), NoncomputableOrd.compare a b = .lt ↔ LT.lt a b := by exact Iff.rfl
  eq_gt_iff_gt : ∀ (a b : α), NoncomputableOrd.compare a b = .gt ↔ LT.lt b a := by exact Iff.rfl

structure Comparable.OfNoncomputableOrdArgs (α : Type u) where
  instNoncomputableOrd : NoncomputableOrd α := by
    try (infer_instance; done)
    try (exact NoncomputableOrd.ofComputable; done)
  instLE : LE α := by
    try (infer_instance; done)
    try (exact LE.ofBLE; done)
    try (exact ⟨fun a b => (compare a b).isLE⟩; done)
  instLT : LT α := by
    try (infer_instance; done)
    try (exact LT.ofBLT; done)
    try (exact ⟨fun a b => compare a b = .lt⟩; done)
  instNoncomputableBEq : NoncomputableBEq α := by
    try (infer_instance; done)
    try (exact NoncomputableBEq.ofComputable; done)
    try (exact NoncomputableBEq.ofRel (fun a b => compare a b = .eq); done)

def Comparable.ofOrd {α : Type u} (args : OfNoncomputableOrdArgs α) : Comparable α where
  toNoncomputableOrd := args.instNoncomputableOrd
  toLE := args.instLE
  toLT := args.instLT
  toNoncomputableBEq := args.instNoncomputableBEq

structure ComputablyComparable.OfOrdArgs (α : Type u) where
  instOrd : Ord α := by
    try (infer_instance; done)
  instNoncomputableOrd : NoncomputableOrd α := by
    try (infer_instance; done)
    try (exact NoncomputableOrd.ofComputable; done)
  instBLE : BLE α := by
    try (infer_instance; done)
    try (exact ⟨fun a b => (compare a b).isLE⟩; done)
  instLE : LE α := by
    try (infer_instance; done)
    try (exact ⟨fun a b => (compare a b).isLE⟩; done)
  instBLT : BLT α := by
    try (infer_instance; done)
    try (exact ⟨fun a b => compare a b = .lt⟩; done)
  instLT : LT α := by
    try (infer_instance; done)
    try (exact ⟨fun a b => compare a b = .lt⟩; done)
  instBEq : BEq α := by
    try (infer_instance; done)
    try (exact ⟨fun a b => compare a b = .eq⟩; done)
  instNoncomputableBEq : NoncomputableBEq α := by
    try (infer_instance; done)
    try (exact NoncomputableBEq.ofRel (fun a b => compare a b = .eq); done)

def ComputablyComparable.ofOrd {α : Type u} (args : OfOrdArgs α) : ComputablyComparable α where
  toOrd := args.instOrd
  toNoncomputableOrd := args.instNoncomputableOrd
  toBLE := args.instBLE
  toLE := args.instLE
  toBLT := args.instBLT
  toLT := args.instLT
  toBEq := args.instBEq
  toNoncomputableBEq := args.instNoncomputableBEq
