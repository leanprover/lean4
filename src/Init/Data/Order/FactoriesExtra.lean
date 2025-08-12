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
  { compare_isLE := by simp [LE.ofOrd]
    compare_isGE := by simp [LE.ofOrd, OrientedCmp.isGE_eq_isLE] }

section Packages

/-!
## Instance packages and factories for them

Instance packages are classes with the sole purpose to bundle together multiple smaller classes.
They should not be used as hypotheses, but they make it more convenient to define multiple instances
at once.
-/

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

/--
This class entails `LE α`, `LT α`, `BEq α` and `Ord α` instances as well as proofs that these
operations represent the same linear preorder structure on `α`.
-/
public class LinearPreorderPackage (α : Type u) extends
    PreorderPackage α, Ord α, LawfulOrderOrd α, IsLinearPreorder α

/--
This structure contains all the data needed to create a `LinearPreorderPackage α` instance. Its fields
are automatically provided if possible. For the detailed rules how the fields are inferred, see
`LinearPreorderPackage.ofLE`.
-/
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

/--
Use this factory to conveniently define a linear preorder on a type `α` and all the associated
operations and instances given an `LE α` instance.

Creates a `LinearPreorderPackage α` instance. Such an instance entails `LE α`, `LT α`, `BEq α` and
`Ord α` instances as well as an `IsLinearPreorder α` instance and `LawfulOrder*` instances proving
the compatibility of the operations with the linear preorder.

In the presence of `LE α`, `DecidableLE α`, `Total (· ≤ ·)` and `Trans (· ≤ ·) (· ≤ ·) (· ≤ ·)`
instances, no arguments are required and the factory can be used as in this example:

```lean
public instance : LinearPreorderPackage X := .ofLE X
```

If not all of these instances are available via typeclass synthesis, it is necessary to explicitly
provide some arguments:

```lean
public instance : LinearPreorderPackage X := .ofLE X {
  le_total := sorry
  le_trans := sorry }
```

It is also possible to do all of this by hand, without resorting to `LinearPreorderPackage`. This
can be useful if, say, one wants to avoid specifying an `LT α` instance, which is not possible with
`LinearPreorderPackage`.

**How the arguments are filled**

Lean tries to fill all of the fields of the `args : Packages.LinearPreorderOfLEArgs α` parameter
automatically. If it fails, it is necessary to provide some of the fields manually.

* For the data-carrying typeclasses `LE`, `LT`, `BEq` and `Ord`, existing instances are always
  preferred. If no existing instances can be synthesized, it is attempted to derive an instance from
  the `LE` instance.
* Some proof obligations can be filled automatically if the data-carrying typeclasses have been
  derived from the `LE` instance. For example: If the `beq` field is omitted and no `BEq α` instance
  can be synthesized, it is derived from the `LE α` instance. In this case, `lawful_beq` can be
  omitted because Lean can infer that `BEq α` and `LE α` are compatible.
* Other proof obligations, namely `le_total` and `le_trans`, can be omitted if `Total` and `Trans`
  instances can be synthesized.
-/
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

/--
Use this factory to conveniently define a linear order on a type `α` and all the associated
operations and instances given an `LE α` instance.

Creates a `LinearPreorderPackage α` instance. Such an instance entails `LE α`, `LT α`, `BEq α` and
`Ord α` instances as well as an `IsLinearPreorder α` instance and `LawfulOrder*` instances proving
the compatibility of the operations with the linear order.

In the presence of `LE α`, `DecidableLE α`, `Total (· ≤ ·)`, `Trans (· ≤ ·) (· ≤ ·) (· ≤ ·)` and
`Antisymm (· ≤ ·)` instances, no arguments are required and the factory can be used as in this
example:

```lean
public instance : LinearPreorderPackage X := .ofLE X
```

If not all of these instances are available via typeclass synthesis, it is necessary to explicitly
provide some arguments:

```lean
public instance : LinearPreorderPackage X := .ofLE X {
  le_total := sorry
  le_trans := sorry
  le_antisymm := sorry }
```

It is also possible to do all of this by hand, without resorting to `LinearOrderPackage`. This
can be useful if, say, one wants to avoid specifying an `LT α` instance, which is not possible with
`LinearOrderPackage`.

**How the arguments are filled**

Lean tries to fill all of the fields of the `args : Packages.LinearOrderOfLEArgs α` parameter
automatically. If it fails, it is necessary to provide some of the fields manually.

* For the data-carrying typeclasses `LE`, `LT`, `BEq` and `Ord`, existing instances are always
  preferred. If no existing instances can be synthesized, it is attempted to derive an instance from
  the `LE` instance.
* Some proof obligations can be filled automatically if the data-carrying typeclasses have been
  derived from the `LE` instance. For example: If the `beq` field is omitted and no `BEq α` instance
  can be synthesized, it is derived from the `LE α` instance. In this case, `lawful_beq` can be
  omitted because Lean can infer that `BEq α` and `LE α` are compatible.
* Other proof obligations, namely `le_total`, `le_trans` and `le_antisymm`, can be omitted if
  `Total`, `Trans` and `Antisymm` instances can be synthesized.
-/
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
