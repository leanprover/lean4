/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Order.ClassesExtra
public import Init.Data.Order.Ord

namespace Std

/--
Creates an `LE α` instance from an `Ord α` instance.

`OrientedOrd α` must be satisfied so that the resulting `LE α` instance faithfully represents
the `Ord α` instance.
-/
public def LE.ofOrd (α : Type u) [Ord α] : LE α where
  le a b := (compare a b).isLE

/--
The `LE α` instance obtained from an `Ord α` instance is compatible with said `Ord α`
instance if `compare` is oriented, i.e., `compare a b = .lt ↔ compare b a = .gt`.
-/
public instance LawfulOrderOrd.of_ord (α : Type u) [Ord α] [OrientedOrd α] :
    haveI := LE.ofOrd α
    LawfulOrderOrd α :=
  letI := LE.ofOrd α
  { isLE_compare := by simp [LE.ofOrd]
    isGE_compare := by simp [LE.ofOrd, OrientedCmp.isGE_eq_isLE] }

section Packages

namespace FactoryInstances

public scoped instance instOrdOfDecidableLE {α : Type u} [LE α] [DecidableLE α] :
    Ord α where
  compare a b := if a ≤ b then if b ≤ a then .eq else .lt else .gt

public theorem compare_isLE {α : Type u} [LE α] [DecidableLE α] {a b : α} :
    (compare a b).isLE ↔ a ≤ b := by
  simp only [compare]
  split
  · split <;> simp_all
  · simp_all

public theorem compare_isGE {α : Type u} [LE α] [DecidableLE α]
    (le_total : ∀ a b : α, a ≤ b ∨ b ≤ a) {a b : α} :
    (compare a b).isGE ↔ b ≤ a := by
  simp only [compare]
  split
  · split <;> simp_all
  · specialize le_total a b
    simp_all

end FactoryInstances

public class LinearPreorderPackage (α : Type u) extends
    PreorderPackage α, Ord α, LawfulOrderOrd α, IsLinearPreorder α

public structure Packages.LinearPreorderOfLEArgs (α : Type u) extends
    PreorderOfLEArgs α where
  ord [i : LE α] [DecidableLE α] (hi : i = le := by rfl) : Ord α := by
    first
      | infer_instance
      | exact fun _ => FactoryInstances.instOrdOfDecidableLE
  le_total : ∀ a b : α, a ≤ b ∨ b ≤ a := by
    first
      | exact Total.total
      | fail "Failed to automatically prove that the `LE` instance is total. You can either ensure \
              that a `Total` instance is available or manually provide the `le_total` field."
  le_refl := (by intro i hi a; cases hi; simpa using le_total a a)
  compare_isLE [i : LE α] [DecidableLE α] (hi : i = le := by rfl) :
      letI := ord hi; ∀ a b : α, (compare a b).isLE ↔ a ≤ b := by
    intro i di hi
    first
      | open scoped Classical in
        simpa only [FactoryInstances.instOrdOfDecidableLE, Ord.compare] using
          fun a b => FactoryInstances.compare_isLE
        done
      | fail "Failed to automatically prove that `(compare a b).isLE` is equivalent to `a ≤ b`."
  compare_isGE [i : LE α] [DecidableLE α] (hi : i = le := by rfl) (le_total := le_total) :
      letI := ord hi; ∀ a b : α, (compare a b).isGE ↔ b ≤ a := by
    intro i di hi
    letI := i
    cases hi
    first
      | open scoped Classical in
        simpa only [FactoryInstances.instOrdOfDecidableLE, Ord.compare] using
          fun le_total a b => FactoryInstances.compare_isGE le_total
        done
      | fail "Failed to automatically prove that `(compare a b).isGE` is equivalent to `b ≤ a`."

@[expose]
public def LinearPreorderPackage.ofLE (α : Type u)
    (args : Packages.LinearPreorderOfLEArgs α := by exact {}) : LinearPreorderPackage α where
  toPreorderPackage := .ofLE α args.toPreorderOfLEArgs
  toOrd := letI := args.le; letI := args.decidableLE; args.ord
  le_total := args.le_total
  compare_isLE := letI := args.le; letI := args.decidableLE; args.compare_isLE
  compare_isGE := letI := args.le; letI := args.decidableLE; args.compare_isGE

namespace FactoryInstances

public scoped instance instMinOfDecidableLE {α : Type u} [LE α] [DecidableLE α] : Min α where
  min a b := if a ≤ b then a else b

public scoped instance instMaxOfDecidableLE {α : Type u} [LE α] [DecidableLE α] : Max α where
  max a b := if a ≤ b then b else a

public theorem min_eq {α : Type u} [LE α] [DecidableLE α] {a b : α} :
    min a b = if a ≤ b then a else b :=
  rfl

public theorem max_eq {α : Type u} [LE α] [DecidableLE α] {a b : α} :
    max a b = if a ≤ b then b else a :=
  rfl

end FactoryInstances

public class LinearOrderPackage (α : Type u) extends
    LinearPreorderPackage α, PartialOrderPackage α, Min α, Max α,
    LawfulOrderMin α, LawfulOrderMax α, IsLinearOrder α

public structure Packages.LinearOrderOfLEArgs (α : Type u) extends
    LinearPreorderOfLEArgs α, PartialOrderOfLEArgs α where
  min [i : LE α] [DecidableLE α] (hi : i = le := by rfl) : Min α := by
    first
      | infer_instance
      | exact fun _ => FactoryInstances.instMinOfDecidableLE
  max [i : LE α] [DecidableLE α] (hi : i = le := by rfl) : Max α := by
    first
      | infer_instance
      | exact fun _ => FactoryInstances.instMaxOfDecidableLE
  min_eq [i : LE α] [DecidableLE α] (hi : i = le := by rfl) :
      letI := min hi
      ∀ a b : α, Min.min a b = if a ≤ b then a else b := by
    intro i d hi
    letI := i
    cases hi
    first
      | infer_instance
      | exact fun _ _ => FactoryInstances.min_eq
  max_eq [i : LE α] [DecidableLE α] (hi : i = le := by rfl) :
      letI := max hi
      ∀ a b : α, Max.max a b = if a ≤ b then b else a := by
    intro i d hi
    letI := i
    cases hi
    first
      | infer_instance
      | exact fun _ _ => FactoryInstances.max_eq

public theorem IsLinearPreorder.lawfulOrderMin_of_min_eq {α : Type u} [LE α]
    [DecidableLE α] [Min α] [IsLinearPreorder α]
    (min_eq : ∀ a b : α, min a b = if a ≤ b then a else b) :
    LawfulOrderMin α where
  min_eq_or a b := by
    rw [min_eq]
    split <;> simp
  le_min_iff a b c := by
    simp only [min_eq]
    split <;> rename_i hbc
    · simp only [iff_self_and]
      exact fun hab => le_trans hab hbc
    · simp only [iff_and_self]
      exact fun hac => le_trans hac (by simpa [hbc] using Std.le_total (a := b) (b := c))

public theorem IsLinearPreorder.lawfulOrderMax_of_max_eq {α : Type u} [LE α]
    [DecidableLE α] [Max α] [IsLinearPreorder α]
    (max_eq : ∀ a b : α, max a b = if a ≤ b then b else a) :
    LawfulOrderMax α where
  max_eq_or a b := by
    rw [max_eq]
    split <;> simp
  max_le_iff a b c := by
    simp only [max_eq]
    split <;> rename_i hab
    · simp only [iff_and_self]
      exact fun hbc => le_trans hab hbc
    · simp only [iff_self_and]
      exact fun hac => le_trans (by simpa [hab] using Std.le_total (a := a) (b := b)) hac

@[expose]
public def LinearOrderPackage.ofLE (α : Type u)
    (args : Packages.LinearOrderOfLEArgs α := by exact {}) : LinearOrderPackage α where
  toLinearPreorderPackage := .ofLE α args.toLinearPreorderOfLEArgs
  le_antisymm := (PartialOrderPackage.ofLE α args.toPartialOrderOfLEArgs).le_antisymm
  toMin := letI := args.le; letI := args.decidableLE; args.min
  toMax := letI := args.le; letI := args.decidableLE; args.max
  toLawfulOrderMin :=
    letI := LinearPreorderPackage.ofLE α args.toLinearPreorderOfLEArgs
    letI := args.decidableLE; letI := args.min
    IsLinearPreorder.lawfulOrderMin_of_min_eq args.min_eq
  toLawfulOrderMax :=
    letI := LinearPreorderPackage.ofLE α args.toLinearPreorderOfLEArgs
    letI := args.decidableLE; letI := args.max
    IsLinearPreorder.lawfulOrderMax_of_max_eq args.max_eq

end Packages

end Std
