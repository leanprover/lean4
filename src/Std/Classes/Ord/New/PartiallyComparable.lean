module

prelude
public import Init.Core
public import Std.Classes.Ord.New.BasicOperations

public section

class PartiallyComparable (α : Type u) extends LT α, LE α, NoncomputableBEq α

instance (α : Type u) [LT α] [LE α] [NoncomputableBEq α] : PartiallyComparable α where

class ComputablyPartiallyComparable α extends PartiallyComparable α, BLE α, BLT α, BEq α

class LawfulPartiallyComparable (α : Type u) [PartiallyComparable α] where
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

@[expose]
def PartiallyComparable.ofLE (args : OfLEArgs α) : PartiallyComparable α where
  toLE := args.instLE
  toLT := args.instLT
  toNoncomputableBEq := args.instNoncomputableBEq

@[expose]
def PartiallyComparable.bltOfBLE (α : Type u) [BLE α] : BLT α where
  LT a b := BLE.LE a b && ! BLE.LE b a

@[expose]
def PartiallyComparable.ltOfBLE (α : Type u) [BLE α] : LT α where
  lt a b := BLE.LE a b ∧ ¬ BLE.LE b a

structure ComputablyPartiallyComparable.OfBLEArgs (α : Type u) where
  instBLE : BLE α := by
    try (infer_instance; done)
  instLE : LE α := by
    try (infer_instance; done)
    try (exact LE.ofBLE α; done)
  instBLT : BLT α := by
    try (infer_instance; done)
    try (exact PartiallyComparable.bltOfBLE α; done)
  instLT : LT α := by
    try (infer_instance; done)
    try (exact PartiallyComparable.ltOfBLE α; done)
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
  letI : PartiallyComparable α := .ofLE {}
  {}

instance (α : Type u) [BLE α] :
    haveI : BLT α := PartiallyComparable.bltOfBLE α
    haveI : LT α := PartiallyComparable.ltOfBLE α
    LawfulBLT α :=
  letI : BLT α := PartiallyComparable.bltOfBLE α
  letI : LT α := PartiallyComparable.ltOfBLE α
  ⟨fun a b => by simp [PartiallyComparable.ltOfBLE, PartiallyComparable.bltOfBLE]⟩

instance (α : Type u) [BLE α] :
    haveI : BLT α := PartiallyComparable.bltOfBLE α
    haveI : LT α := PartiallyComparable.ltOfBLE α
    LawfulBLT α :=
  letI : BLT α := PartiallyComparable.bltOfBLE α
  letI : LT α := PartiallyComparable.ltOfBLE α
  ⟨fun a b => by simp [PartiallyComparable.ltOfBLE, PartiallyComparable.bltOfBLE]⟩

-- use like this:
-- instance (α : Type u) [BLE α] : ComputablyPartiallyComparable α := .ofBLE {}
