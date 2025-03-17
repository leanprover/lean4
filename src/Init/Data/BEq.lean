/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Markus Himmel
-/
prelude
import Init.Data.Bool

set_option linter.missingDocs true

/-- `PartialEquivBEq α` says that the `BEq` implementation is a
partial equivalence relation, that is:
* it is symmetric: `a == b → b == a`
* it is transitive: `a == b → b == c → a == c`.
-/
class PartialEquivBEq (α) [BEq α] : Prop where
  /-- Symmetry for `BEq`. If `a == b` then `b == a`. -/
  symm : (a : α) == b → b == a
  /-- Transitivity for `BEq`. If `a == b` and `b == c` then `a == c`. -/
  trans : (a : α) == b → b == c → a == c

/-- `ReflBEq α` says that the `BEq` implementation is reflexive. -/
class ReflBEq (α) [BEq α] : Prop where
  /-- Reflexivity for `BEq`. -/
  refl : (a : α) == a

/-- `EquivBEq` says that the `BEq` implementation is an equivalence relation. -/
class EquivBEq (α) [BEq α] : Prop extends PartialEquivBEq α, ReflBEq α

@[simp]
theorem BEq.refl [BEq α] [ReflBEq α] {a : α} : a == a :=
  ReflBEq.refl

theorem beq_of_eq [BEq α] [ReflBEq α] {a b : α} : a = b → a == b
  | rfl => BEq.refl

theorem BEq.symm [BEq α] [PartialEquivBEq α] {a b : α} : a == b → b == a :=
  PartialEquivBEq.symm

theorem BEq.comm [BEq α] [PartialEquivBEq α] {a b : α} : (a == b) = (b == a) :=
  Bool.eq_iff_iff.2 ⟨BEq.symm, BEq.symm⟩

theorem bne_comm [BEq α] [PartialEquivBEq α] {a b : α} : (a != b) = (b != a) := by
  rw [bne, BEq.comm, bne]

theorem BEq.symm_false [BEq α] [PartialEquivBEq α] {a b : α} : (a == b) = false → (b == a) = false :=
  BEq.comm (α := α) ▸ id

theorem BEq.trans [BEq α] [PartialEquivBEq α] {a b c : α} : a == b → b == c → a == c :=
  PartialEquivBEq.trans

theorem BEq.congr_left [BEq α] [PartialEquivBEq α] {a b c : α} (h : a == b) :
    (a == c) = (b == c) :=
  Bool.eq_iff_iff.mpr ⟨BEq.trans (BEq.symm h), BEq.trans h⟩

theorem BEq.congr_right [BEq α] [PartialEquivBEq α] {a b c : α} (h : b == c) :
    (a == b) = (a == c) :=
  Bool.eq_iff_iff.mpr ⟨fun h' => BEq.trans h' h, fun h' => BEq.trans h' (BEq.symm h)⟩

theorem BEq.neq_of_neq_of_beq [BEq α] [PartialEquivBEq α] {a b c : α} :
    (a == b) = false → b == c → (a == c) = false :=
  fun h₁ h₂ => Bool.eq_false_iff.2 fun h₃ => Bool.eq_false_iff.1 h₁ (BEq.trans h₃ (BEq.symm h₂))

theorem BEq.neq_of_beq_of_neq [BEq α] [PartialEquivBEq α] {a b c : α} :
    a == b → (b == c) = false → (a == c) = false :=
  fun h₁ h₂ => Bool.eq_false_iff.2 fun h₃ => Bool.eq_false_iff.1 h₂ (BEq.trans (BEq.symm h₁) h₃)

instance (priority := low) [BEq α] [LawfulBEq α] : EquivBEq α where
  refl := LawfulBEq.rfl
  symm h := beq_iff_eq.2 <| Eq.symm <| beq_iff_eq.1 h
  trans hab hbc := beq_iff_eq.2 <| (beq_iff_eq.1 hab).trans <| beq_iff_eq.1 hbc
