module

prelude
public import Init.Core
public import Std.Classes.Ord.New.BasicOperations

public section

class PartiallyComparableMixin (α : Type u) [LT α] [LE α] [NoncomputableBEq α] : Prop

class PartiallyComparable (α : Type u) extends LT α, LE α, NoncomputableBEq α,
    PartiallyComparableMixin α

class ComputablyPartiallyComparable α extends PartiallyComparable α, BLE α, BLT α, BEq α

class LawfulPartiallyComparable (α : Type u) [LT α] [LE α] [NoncomputableBEq α] where
    lt_iff_le_not_ge : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬ b ≤ a := by exact fun _ _ => Iff.rfl

structure PartiallyComparable.OfLEArgs (α : Type u) where
  instLE : LE α := by
    try (infer_instance; done)
    try (exact LE.ofBLE; done)
  instLT : LT α := by
    try (infer_instance; done)
    try (exact LT.ofBLT; done)
    try (exact ⟨fun a b => a ≤ b ∧ ¬ b ≤ a⟩; done)
  instNoncomputableBEq : NoncomputableBEq α := by
    try (infer_instance; done)
    try (exact NoncomputableBEq.ofComputable; done)
    try (exact NoncomputableBEq.ofRel fun a b => a ≤ b ∧ b ≤ a; done)

def PartiallyComparable.ofLE (args : OfLEArgs α) : PartiallyComparable α where
  toLE := args.instLE
  toLT := args.instLT
  toNoncomputableBEq := args.instNoncomputableBEq

structure ComputablyPartiallyComparable.OfBLEArgs (α : Type u) where
  instBLE : BLE α := by
    try (infer_instance; done)
  instLE : LE α := by
    try (infer_instance; done)
    try (exact LE.ofBLE α; done)
  instBLT : BLT α := by
    try (infer_instance; done)
    try (exact ⟨fun a b => BLE.LE a b && ! BLE.LE b a⟩; done)
  instLT : LT α := by
    try (infer_instance; done)
    try (exact ⟨fun a b => BLE.LE a b ∧ ¬ BLE.LE a b⟩; done)
  instBEq : BEq α := by
    try (infer_instance; done)
    try (exact ⟨fun a b => BLE.LE a b ∧ BLE.LE b a⟩; done)
  instNoncomputableBEq : NoncomputableBEq α := by
    try (infer_instance; done)
    try (exact NoncomputableBEq.ofComputable; done)
    try (exact NoncomputableBEq.ofRel fun a b => BLE.LE a b && BLE.LE b a; done)

def ComputablyPartiallyComparable.ofBLE (args : OfBLEArgs α) : ComputablyPartiallyComparable α where
  toBLE := args.instBLE
  toLE := args.instLE
  toBLT := args.instBLT
  toLT := args.instLT
  toBEq := args.instBEq
  toNoncomputableBEq := args.instNoncomputableBEq

instance PartiallyComparable.lawful [LE α] :
    haveI : PartiallyComparable α := .ofLE {}
    LawfulPartiallyComparable α :=
  letI : PartiallyComparable α := .ofLE {}; {}

-- use like this:
-- instance (α : Type u) [BLE α] : ComputablyPartiallyComparable α := .ofBLE {}
