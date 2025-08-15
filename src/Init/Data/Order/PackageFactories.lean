/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Order.FactoriesExtra
public import Init.Data.Order.LemmasExtra

namespace Std

/-!
## Instance packages and factories for them

Instance packages are classes with the sole purpose to bundle together multiple smaller classes.
They should not be used as hypotheses, but they make it more convenient to define multiple instances
at once.
-/

section Preorder

/--
This class entails `LE α`, `LT α` and `BEq α` instances as well as proofs that these operations
represent the same preorder structure on `α`.
-/
public class PreorderPackage (α : Type u) extends
    LE α, LT α, BEq α, LawfulOrderLT α, LawfulOrderBEq α, IsPreorder α where
  decidableLE : DecidableLE α
  decidableLT : DecidableLT α

public instance [PreorderPackage α] : DecidableLE α := PreorderPackage.decidableLE
public instance [PreorderPackage α] : DecidableLT α := PreorderPackage.decidableLT

namespace FactoryInstances

public scoped instance instBEqOfDecidableLE {α : Type u} [LE α] [DecidableLE α] :
    BEq α where
  beq a b := a ≤ b ∧ b ≤ a

public instance instLawfulOrderBEqOfDecidableLE {α : Type u} [LE α] [DecidableLE α] :
    LawfulOrderBEq α where
  beq_iff_le_and_ge := by simp [BEq.beq]

/-- If `LT` can be characterized in terms of a decidable `LE`, then `LT` is decidable either. -/
@[expose]
public def instDecidableLTOfLE {α : Type u} [LE α] {_ : LT α} [DecidableLE α] [LawfulOrderLT α] :
    DecidableLT α :=
  fun a b =>
    haveI := iff_iff_eq.mp <| LawfulOrderLT.lt_iff a b
    if h : a ≤ b ∧ ¬ b ≤ a then .isTrue (this ▸ h) else .isFalse (this ▸ h)

end FactoryInstances

/--
This structure contains all the data needed to create a `PreorderPackage α` instance. Its fields
are automatically provided if possible. For the detailed rules how the fields are inferred, see
`PreorderPackage.ofLE`.
-/
public structure Packages.PreorderOfLEArgs (α : Type u) where
  le : LE α := by infer_instance
  decidableLE : DecidableLE α := by infer_instance
  lt :
      let := le
      LT α := by
    extract_lets
    first
      | infer_instance
      | exact Classical.Order.instLT
  beq :
      let := le; let := decidableLE
      BEq α := by
    extract_lets
    first
      | infer_instance
      | exact FactoryInstances.instBEqOfDecidableLE
  lawful_lt :
      let := le; let := lt
      ∀ a b : α, a < b ↔ a ≤ b ∧ ¬ b ≤ a := by
    extract_lets
    first
      | exact LawfulOrderLT.lt_iff
      | fail "Failed to automatically prove that the `OrderData` and `LT` instances are compatible."
  decidableLT :
      let := le; let := decidableLE; let := lt; haveI := lawful_lt
      have := lawful_lt
      DecidableLT α := by
    extract_lets
    haveI := @LawfulOrderLT.mk (lt_iff := by assumption) ..
    first
      | infer_instance
      | exact FactoryInstances.instDecidableLTOfLE
      | fail "Failed to automatically derive a `DecidableLT` instance."
  lawful_beq :
      let := le; let := decidableLE; let := beq
      ∀ a b : α, a == b ↔ a ≤ b ∧ b ≤ a := by
    extract_lets
    first
      | exact LawfulOrderBEq.beq_iff_le_and_ge
      | fail "Failed to automatically prove that the `OrderData` and `BEq` instances are compatible."
  le_refl :
      let := le
      ∀ a : α, a ≤ a := by
    extract_lets
    first
      | exact Std.Refl.refl (r := (· ≤ ·))
      | fail "Failed to automatically prove that the `LE` instance is reflexive."
  le_trans :
      let := le
      ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c := by
    extract_lets
    first
      | exact fun _ _ _ hab hbc => Trans.trans (r := (· ≤ ·)) (s := (· ≤ ·)) (t := (· ≤ ·)) hab hbc
      | fail "Failed to automatically prove that the `LE` instance is transitive."

/--
Use this factory to conveniently define a preorder on a type `α` and all the associated operations
and instances given an `LE α` instance.

Creates a `PreorderPackage α` instance. Such an instance entails `LE α`, `LT α` and
`BEq α` instances as well as an `IsPreorder α` instance and `LawfulOrder*` instances proving the
compatibility of the operations with the preorder.

In the presence of `LE α`, `DecidableLE α`, `Refl (· ≤ ·)` and `Trans (· ≤ ·) (· ≤ ·) (· ≤ ·)`
instances, no arguments are required and the factory can be used as in this example:

```lean
public instance : PreorderPackage X := .ofLE X
```

If not all of these instances are available via typeclass synthesis, it is necessary to explicitly
provide some arguments:

```lean
public instance : PreorderPackage X := .ofLE X {
  le_refl := sorry
  le_trans := sorry }
```

It is also possible to do all of this by hand, without resorting to `PreorderPackage`. This can
be useful if, say, one wants to avoid specifying an `LT α` instance, which is not possible with
`PreorderPackage`.

**How the arguments are filled**

Lean tries to fill all of the fields of the `args : Packages.PreorderOfLEArgs α` parameter
automatically. If it fails, it is necessary to provide some of the fields manually.

* For the data-carrying typeclasses `LE`, `LT` and `BEq`, existing instances are always preferred.
  If no existing instances can be synthesized, it is attempted to derive an instance from the `LE`
  instance.
* Some proof obligations can be filled automatically if the data-carrying typeclasses have been
  derived from the `LE` instance. For example: If the `beq` field is omitted and no `BEq α` instance
  can be synthesized, it is derived from the `LE α` instance. In this case, `lawful_beq` can be
  omitted because Lean can infer that `BEq α` and `LE α` are compatible.
* Other proof obligations, namely `le_refl` and `le_trans`, can be omitted if `Refl` and `Trans`
  instances can be synthesized.
-/
@[expose]
public def PreorderPackage.ofLE (α : Type u)
    (args : Packages.PreorderOfLEArgs α := by exact {}) : PreorderPackage α where
  toLE := args.le
  decidableLE := args.decidableLE
  toLT := args.lt
  toBEq := args.beq
  toLawfulOrderLT := @LawfulOrderLT.mk (lt_iff := args.lawful_lt)
  decidableLT := args.decidableLT
  toLawfulOrderBEq := @LawfulOrderBEq.mk (beq_iff_le_and_ge := args.lawful_beq)
  le_refl := args.le_refl
  le_trans := args.le_trans

end Preorder

section PartialOrder

/--
This class entails `LE α`, `LT α` and `BEq α` instances as well as proofs that these operations
represent the same partial order structure on `α`.
-/
public class PartialOrderPackage (α : Type u) extends
    PreorderPackage α, IsPartialOrder α

/--
This structure contains all the data needed to create a `PartialOrderPakckage α` instance. Its
fields are automatically provided if possible. For the detailed rules how the fields are inferred,
see `PartialOrderPackage.ofLE`.
-/
public structure Packages.PartialOrderOfLEArgs (α : Type u) extends Packages.PreorderOfLEArgs α where
  le_antisymm :
      let := le
      ∀ a b : α, a ≤ b → b ≤ a → a = b := by
    extract_lets
    first
      | exact Antisymm.antisymm
      | fail "Failed to automatically prove that the `LE` instance is antisymmetric. You can either ensure that an `Asymm` instance is available or manually provide the `le_antisymm` field."

/-
Use this factory to conveniently define a partial order on a type `α` and all the associated
operations and instances given an `LE α` instance.

Creates a `PartialOrderPackage α` instance. Such an instance entails `LE α`, `LT α` and
`BEq α` instances as well as an `IsPartialOrder α` instance and `LawfulOrder*` instances proving the
compatibility of the operations with the preorder.

In the presence of `LE α`, `DecidableLE α`, `Refl (· ≤ ·)`, `Trans (· ≤ ·) (· ≤ ·) (· ≤ ·)`
and `Antisymm (· ≤ ·)` instances, no arguments are required and the factory can be used as in this
example:

```lean
public instance : PartialOrderPackage X := .ofLE X
```

If not all of these instances are available via typeclass synthesis, it is necessary to explicitly
provide some arguments:

```lean
public instance : PartialOrderPackage X := .ofLE X {
  le_refl := sorry
  le_trans := sorry
  le_antisymm := sorry }
```

It is also possible to do all of this by hand, without resorting to `PartialOrderPackage`. This can
be useful if, say, one wants to avoid specifying an `LT α` instance, which is not possible with
`PartialOrderPackage`.

**How the arguments are filled**

Lean tries to fill all of the fields of the `args : Packages.PartialOrderOfLEArgs α` parameter
automatically. If it fails, it is necessary to provide some of the fields manually.

* For the data-carrying typeclasses `LE`, `LT` and `BEq`, existing instances are always preferred.
  If no existing instances can be synthesized, it is attempted to derive an instance from the `LE`
  instance.
* Some proof obligations can be filled automatically if the data-carrying typeclasses have been
  derived from the `LE` instance. For example: If the `beq` field is omitted and no `BEq α` instance
  can be synthesized, it is derived from the `LE α` instance. In this case, `lawful_beq` can be
  omitted because Lean can infer that `BEq α` and `LE α` are compatible.
* Other proof obligations, namely `le_refl`, `le_trans` and `le_antisymm`, can be omitted if `Refl`,
  `Trans` and `Antisymm` instances can be synthesized.
-/
@[expose]
public def PartialOrderPackage.ofLE (α : Type u)
    (args : Packages.PartialOrderOfLEArgs α := by exact {}) : PartialOrderPackage α where
  toPreorderPackage := .ofLE α args.toPreorderOfLEArgs
  le_antisymm := args.le_antisymm

end PartialOrder

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

public instance instLawfulOrderOrdOfDecidableLE {α : Type u} [LE α] [DecidableLE α]
    [Total (α := α) (· ≤ ·)] :
    LawfulOrderOrd α where
  compare_isLE _ _ := compare_isLE
  compare_isGE _ _ := compare_isGE (le_total := Total.total)

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
  ord :
      let := le; let := decidableLE
      Ord α := by
    extract_lets
    first
      | infer_instance
      | exact FactoryInstances.instOrdOfDecidableLE
  le_total :
      ∀ a b : α, a ≤ b ∨ b ≤ a := by
    first
      | exact Total.total
      | fail "Failed to automatically prove that the `LE` instance is total. You can either ensure \
              that a `Total` instance is available or manually provide the `le_total` field."
  le_refl a := (by simpa using le_total a a)
  compare_isLE :
      let := le; let := decidableLE; let := ord
      ∀ a b : α, (compare a b).isLE ↔ a ≤ b := by
    extract_lets
    first
      | exact LawfulOrderOrd.compare_isLE
      | open scoped Classical in
        simpa only [FactoryInstances.instOrdOfDecidableLE, Ord.compare] using
          fun a b => FactoryInstances.compare_isLE
        done
      | fail "Failed to automatically prove that `(compare a b).isLE` is equivalent to `a ≤ b`."
  compare_isGE :
      let := le; let := decidableLE; have := le_total; let := ord
      ∀ a b : α, (compare a b).isGE ↔ b ≤ a := by
    extract_lets
    first
      | exact LawfulOrderOrd.compare_isGE
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
  toOrd := letI := args.le; args.ord
  le_total := args.le_total
  compare_isLE := args.compare_isLE
  compare_isGE := args.compare_isGE

namespace FactoryInstances

public scoped instance instMinOfDecidableLE {α : Type u} [LE α] [DecidableLE α] : Min α where
  min a b := if a ≤ b then a else b

public scoped instance instMaxOfDecidableLE {α : Type u} [LE α] [DecidableLE α] : Max α where
  max a b := if b ≤ a then a else b

public instance instLawfulOrderLeftLeaningMinOfDecidableLE {α : Type u} [LE α] [DecidableLE α] :
    LawfulOrderLeftLeaningMin α where
  min_eq_left a b := by simp +contextual [min]
  min_eq_right a b := by simp +contextual [min]

public instance instLawfulOrderLeftLeaningMaxOfDecidableLE {α : Type u} [LE α] [DecidableLE α] :
    LawfulOrderLeftLeaningMax α where
  max_eq_left a b := by simp +contextual [max]
  max_eq_right a b := by simp +contextual [max]

end FactoryInstances

/--
This class entails `LE α`, `LT α`, `BEq α`, `Ord α`, `Min α` and `Max α` instances as well as proofs
that these operations represent the same linear order structure on `α`.
-/
public class LinearOrderPackage (α : Type u) extends
    LinearPreorderPackage α, PartialOrderPackage α, Min α, Max α,
    LawfulOrderMin α, LawfulOrderMax α, IsLinearOrder α

/--
This structure contains all the data needed to create a `LinearOrderPackage α` instance. Its fields
are automatically provided if possible. For the detailed rules how the fields are inferred, see
`LinearOrderPackage.ofLE`.
-/
public structure Packages.LinearOrderOfLEArgs (α : Type u) extends
    LinearPreorderOfLEArgs α, PartialOrderOfLEArgs α where
  min :
      let := le; let := decidableLE
      Min α := by
    extract_lets
    first
      | infer_instance
      | exact FactoryInstances.instMinOfDecidableLE
  max :
      let := le; let := decidableLE
      Max α := by
    extract_lets
    first
      | infer_instance
      | exact FactoryInstances.instMaxOfDecidableLE
  min_eq :
      let := le; let := decidableLE; let := min
      ∀ a b : α, Min.min a b = if a ≤ b then a else b := by
    extract_lets
    first
      | exact fun a b => Std.min_eq_if_le (a := a) (b := b)
      | fail "Failed to automatically prove that `min` is left-leaning. Provide `min_eq` manually."
  max_eq :
      let := le; let := decidableLE; let := max
      ∀ a b : α, Max.max a b = if b ≤ a then a else b := by
    extract_lets
    first
      | exact fun a b => Std.max_eq_if_ge (a := a) (b := b)
      | fail "Failed to automatically prove that `max` is left-leaning. Provide `max_eq` manually."

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
    (max_eq : ∀ a b : α, max a b = if b ≤ a then a else b) :
    LawfulOrderMax α where
  max_eq_or a b := by
    rw [max_eq]
    split <;> simp
  max_le_iff a b c := by
    simp only [max_eq]
    split <;> rename_i hab
    · simp only [iff_self_and]
      exact fun hbc => le_trans hab hbc
    · simp only [iff_and_self]
      exact fun hac => le_trans (by simpa [hab] using Std.le_total (a := a) (b := b)) hac

/--
Use this factory to conveniently define a linear order on a type `α` and all the associated
operations and instances given an `LE α` instance.

Creates a `LinearOrderPackage α` instance. Such an instance entails `LE α`, `LT α`, `BEq α`,
`Ord α`, `Min α` and `Max α` instances as well as an `IsLinearOrder α` instance and `LawfulOrder*`
instances proving the compatibility of the operations with the linear order.

In the presence of `LE α`, `DecidableLE α`, `Total (· ≤ ·)`, `Trans (· ≤ ·) (· ≤ ·) (· ≤ ·)` and
`Antisymm (· ≤ ·)` instances, no arguments are required and the factory can be used as in this
example:

```lean
public instance : LinearOrderPackage X := .ofLE X
```

If not all of these instances are available via typeclass synthesis, it is necessary to explicitly
provide some arguments:

```lean
public instance : LinearOrderPackage X := .ofLE X {
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

* For the data-carrying typeclasses `LE`, `LT`, `BEq`, `Ord`, `Min` and `Max`, existing instances
  are always preferred. If no existing instances can be synthesized, it is attempted to derive an
  instance from the `LE` instance.
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
  toMin := args.min
  toMax := args.max
  toLawfulOrderMin :=
    letI := LinearPreorderPackage.ofLE α args.toLinearPreorderOfLEArgs
    letI := args.decidableLE; letI := args.min
    IsLinearPreorder.lawfulOrderMin_of_min_eq args.min_eq
  toLawfulOrderMax :=
    letI := LinearPreorderPackage.ofLE α args.toLinearPreorderOfLEArgs
    letI := args.decidableLE; letI := args.max
    IsLinearPreorder.lawfulOrderMax_of_max_eq args.max_eq

end Std
