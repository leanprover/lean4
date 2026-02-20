/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Order.LemmasExtra  -- shake: keep (instance inlined by `haveI`)
public import Init.Data.Order.FactoriesExtra
import Init.Data.Bool
import Init.Data.Order.Lemmas

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

public scoped instance beqOfDecidableLE {α : Type u} [LE α] [DecidableLE α] :
    BEq α where
  beq a b := a ≤ b ∧ b ≤ a

public instance instLawfulOrderBEqOfDecidableLE {α : Type u} [LE α] [DecidableLE α] :
    LawfulOrderBEq α where
  beq_iff_le_and_ge := by simp [BEq.beq]

/-- If `LT` can be characterized in terms of a decidable `LE`, then `LT` is decidable either. -/
@[expose, instance_reducible]
public def decidableLTOfLE {α : Type u} [LE α] {_ : LT α} [DecidableLE α] [LawfulOrderLT α] :
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
    | exact _root_.Classical.Order.instLT
  beq :
    let := le; let := decidableLE
    BEq α := by
    extract_lets
    first
    | infer_instance
    | exact _root_.Std.FactoryInstances.beqOfDecidableLE
  lt_iff :
      let := le; let := lt
      ∀ a b : α, a < b ↔ a ≤ b ∧ ¬ b ≤ a := by
    extract_lets
    first
    | exact _root_.Std.LawfulOrderLT.lt_iff
    | fail "Failed to automatically prove that the `LE` and `LT` instances are compatible. \
            Please ensure that a `LawfulOrderLT` instance can be synthesized or \
            manually provide the field `lt_iff`."
  decidableLT :
      let := le; let := decidableLE; let := lt; haveI := lt_iff
      have := lt_iff
      DecidableLT α := by
    extract_lets
    haveI := @_root_.Std.LawfulOrderLT.mk (lt_iff := by assumption) ..
    first
    | infer_instance
    | exact _root_.Std.FactoryInstances.decidableLTOfLE
    | fail "Failed to automatically derive that `LT` is decidable. \
            Please ensure that a `DecidableLT` instance can be synthesized or \
            manually provide the field `decidableLT`."
  beq_iff_le_and_ge :
      let := le; let := decidableLE; let := beq
      ∀ a b : α, a == b ↔ a ≤ b ∧ b ≤ a := by
    extract_lets
    first
      | exact _root_.Std.LawfulOrderBEq.beq_iff_le_and_ge
      | fail "Failed to automatically prove that the `LE` and `BEq` instances are compatible. \
              Please ensure that a `LawfulOrderBEq` instance can be synthesized or \
              manually provide the field `beq_iff_le_and_ge`."
  le_refl :
      let := le
      ∀ a : α, a ≤ a := by
    extract_lets
    first
    | exact _root_.Std.Refl.refl (r := (· ≤ ·))
    | fail "Failed to automatically prove that the `LE` instance is reflexive. \
            Please ensure that a `Refl` instance can be synthesized or \
            manually provide the field `le_refl`."
  le_trans :
      let := le
      ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c := by
    extract_lets
    first
    | exact fun _ _ _ hab hbc => _root_.Trans.trans (r := (· ≤ ·)) (s := (· ≤ ·)) (t := (· ≤ ·)) hab hbc
    | fail "Failed to automatically prove that the `LE` instance is transitive. \
            Please ensure that a `Trans` instance can be synthesized or \
            manually provide the field `le_trans`."

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
  can be synthesized, it is derived from the `LE α` instance. In this case, `beq_iff_le_and_ge` can
  be omitted because Lean can infer that `BEq α` and `LE α` are compatible.
* Other proof obligations, namely `le_refl` and `le_trans`, can be omitted if `Refl` and `Trans`
  instances can be synthesized.
-/
@[expose, instance_reducible]
public def PreorderPackage.ofLE (α : Type u)
    (args : Packages.PreorderOfLEArgs α := by exact {}) : PreorderPackage α where
  toLE := args.le
  decidableLE := args.decidableLE
  toLT := args.lt
  toBEq := args.beq
  toLawfulOrderLT := @LawfulOrderLT.mk (lt_iff := args.lt_iff)
  decidableLT := args.decidableLT
  toLawfulOrderBEq := @LawfulOrderBEq.mk (beq_iff_le_and_ge := args.beq_iff_le_and_ge)
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
    | exact _root_.Std.Antisymm.antisymm
    | fail "Failed to automatically prove that the `LE` instance is antisymmetric. \
            Please ensure that a `Antisymm` instance can be synthesized or \
            manually provide the field `le_antisymm`."

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
  can be synthesized, it is derived from the `LE α` instance. In this case, `beq_iff_le_and_ge` can be
  omitted because Lean can infer that `BEq α` and `LE α` are compatible.
* Other proof obligations, namely `le_refl`, `le_trans` and `le_antisymm`, can be omitted if `Refl`,
  `Trans` and `Antisymm` instances can be synthesized.
-/
@[expose, instance_reducible]
public def PartialOrderPackage.ofLE (α : Type u)
    (args : Packages.PartialOrderOfLEArgs α := by exact {}) : PartialOrderPackage α where
  toPreorderPackage := .ofLE α args.toPreorderOfLEArgs
  le_antisymm := args.le_antisymm

end PartialOrder

namespace FactoryInstances

public scoped instance instOrdOfDecidableLE {α : Type u} [LE α] [DecidableLE α] :
    Ord α where
  compare a b := if a ≤ b then if b ≤ a then .eq else .lt else .gt

theorem isLE_compare {α : Type u} [LE α] [DecidableLE α] {a b : α} :
    (compare a b).isLE ↔ a ≤ b := by
  simp only [compare]
  split
  · split <;> simp_all
  · simp_all

theorem isGE_compare {α : Type u} [LE α] [DecidableLE α]
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
  isLE_compare _ _ := by exact isLE_compare
  isGE_compare _ _ := by exact isGE_compare (le_total := Total.total)

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
    | exact _root_.Std.FactoryInstances.instOrdOfDecidableLE
  le_total :
      ∀ a b : α, a ≤ b ∨ b ≤ a := by
    first
    | exact _root_.Std.Total.total
    | fail "Failed to automatically prove that the `LE` instance is total. \
            Please ensure that a `Total` instance can be synthesized or \
            manually provide the field `le_total`."
  le_refl a := (by simpa using le_total a a)
  isLE_compare :
      let := le; let := decidableLE; let := ord
      ∀ a b : α, (compare a b).isLE ↔ a ≤ b := by
    extract_lets
    first
    | exact _root_.Std.LawfulOrderOrd.isLE_compare
    | fail "Failed to automatically prove that `(compare a b).isLE` is equivalent to `a ≤ b`. \
            Please ensure that a `LawfulOrderOrd` instance can be synthesized or \
            manually provide the field `isLE_compare`."
  isGE_compare :
      let := le; let := decidableLE; have := le_total; let := ord
      ∀ a b : α, (compare a b).isGE ↔ b ≤ a := by
    extract_lets
    first
    | exact _root_.Std.LawfulOrderOrd.isGE_compare
    | fail "Failed to automatically prove that `(compare a b).isGE` is equivalent to `b ≤ a`. \
            Please ensure that a `LawfulOrderOrd` instance can be synthesized or \
            manually provide the field `isGE_compare`."

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
  can be synthesized, it is derived from the `LE α` instance. In this case, `beq_iff_le_and_ge` can be
  omitted because Lean can infer that `BEq α` and `LE α` are compatible.
* Other proof obligations, namely `le_total` and `le_trans`, can be omitted if `Total` and `Trans`
  instances can be synthesized.
-/
@[expose, instance_reducible]
public def LinearPreorderPackage.ofLE (α : Type u)
    (args : Packages.LinearPreorderOfLEArgs α := by exact {}) : LinearPreorderPackage α where
  toPreorderPackage := .ofLE α args.toPreorderOfLEArgs
  toOrd := letI := args.le; args.ord
  le_total := args.le_total
  isLE_compare := args.isLE_compare
  isGE_compare := args.isGE_compare

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
    | exact _root_.Min.leftLeaningOfLE _
  max :
      let := le; let := decidableLE
      Max α := by
    extract_lets
    first
    | infer_instance
    | exact _root_.Max.leftLeaningOfLE _
  min_eq :
      let := le; let := decidableLE; let := min
      ∀ a b : α, Min.min a b = if a ≤ b then a else b := by
    extract_lets
    first
    | exact fun a b => _root_.Std.min_eq_if (a := a) (b := b)
    | fail "Failed to automatically prove that `min` is left-leaning. \
            Please ensure that a `LawfulOrderLeftLeaningMin` instance can be synthesized or \
            manually provide the field `min_eq`."
  max_eq :
      let := le; let := decidableLE; let := max
      ∀ a b : α, Max.max a b = if b ≤ a then a else b := by
    extract_lets
    first
    | exact fun a b => _root_.Std.max_eq_if (a := a) (b := b)
    | fail "Failed to automatically prove that `max` is left-leaning. \
            Please ensure that a `LawfulOrderLeftLeaningMax` instance can be synthesized or \
            manually provide the field `max_eq`."

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
  can be synthesized, it is derived from the `LE α` instance. In this case, `beq_iff_le_and_ge` can be
  omitted because Lean can infer that `BEq α` and `LE α` are compatible.
* Other proof obligations, namely `le_total`, `le_trans` and `le_antisymm`, can be omitted if
  `Total`, `Trans` and `Antisymm` instances can be synthesized.
-/
@[expose, instance_reducible]
public def LinearOrderPackage.ofLE (α : Type u)
    (args : Packages.LinearOrderOfLEArgs α := by exact {}) : LinearOrderPackage α where
  toLinearPreorderPackage := .ofLE α args.toLinearPreorderOfLEArgs
  le_antisymm := (PartialOrderPackage.ofLE α args.toPartialOrderOfLEArgs).le_antisymm
  toMin := args.min
  toMax := args.max
  toLawfulOrderMin := by
    letI := LinearPreorderPackage.ofLE α args.toLinearPreorderOfLEArgs
    letI := args.decidableLE; letI := args.min
    haveI : LawfulOrderLeftLeaningMin α := .of_eq args.min_eq
    infer_instance
  toLawfulOrderMax := by
    letI := LinearPreorderPackage.ofLE α args.toLinearPreorderOfLEArgs
    letI := args.decidableLE; letI := args.max
    haveI : LawfulOrderLeftLeaningMax α := .of_eq args.max_eq
    infer_instance

section LinearPreorder

namespace FactoryInstances

attribute [scoped instance] LE.ofOrd
attribute [scoped instance] LT.ofOrd
attribute [scoped instance] BEq.ofOrd

public theorem _root_.Std.OrientedCmp.of_gt_iff_lt {α : Type u} {cmp : α → α → Ordering}
    (h : ∀ a b : α, cmp a b = .gt ↔ cmp b a = .lt) : OrientedCmp cmp where
  eq_swap {a b} := by
    cases h' : cmp a b
    · apply Eq.symm
      simp [h, h']
    · cases h'' : cmp b a
      · simp [← h, h'] at h''
      · simp
      · simp [h, h'] at h''
    · apply Eq.symm
      simp [← h, h']

end FactoryInstances

/--
This structure contains all the data needed to create a `LinearPreorderPackage α` instance.
Its fields are automatically provided if possible. For the detailed rules how the fields are
inferred, see `LinearPreorderPackage.ofOrd`.
-/
public structure Packages.LinearPreorderOfOrdArgs (α : Type u) where
  ord : Ord α := by infer_instance
  transOrd  : TransOrd α := by infer_instance
  le :
      let := ord
      LE α := by
    extract_lets
    first
    | infer_instance
    | exact _root_.LE.ofOrd _
  lawfulOrderOrd :
      let := ord; let := transOrd; let := le
      LawfulOrderOrd α := by
    extract_lets
    first
    | infer_instance
    | fail "Failed to automatically derive a `LawfulOrderOrd` instance. \
            Please ensure that the instance can be synthesized or \
            manually provide the field `lawfulOrderOrd`."
  decidableLE :
      let := ord; let := le; have := lawfulOrderOrd
      DecidableLE α := by
    extract_lets
    first
    | infer_instance
    | exact _root_.DecidableLE.ofOrd _
    | fail "Failed to automatically derive that `LE` is decidable.\
            Please ensure that a `DecidableLE` instance can be synthesized or \
            manually provide the field `decidableLE`."
  lt :
      let := ord
      LT α := by
    extract_lets
    first
    | infer_instance
    | exact LT.ofOrd _
  lt_iff :
      let := ord; let := le; have := lawfulOrderOrd; let := lt
      ∀ a b : α, a < b ↔ compare a b = .lt := by
    extract_lets
    first
    | exact fun _ _ => _root_.Std.compare_eq_lt.symm
    | fail "Failed to automatically derive that `LT` and `Ord` are compatible. \
            Please ensure that a `LawfulOrderLT` instance can be synthesized or \
            manually provide the field `lt_iff`."
  decidableLT :
      let := ord; let := lt; let := le; have := lawfulOrderOrd; have := lt_iff
      DecidableLT α := by
    extract_lets
    first
    | infer_instance
    | exact _root_DecidableLT.ofOrd _
    | fail "Failed to automatically derive that `LT` is decidable. \
            Please ensure that a `DecidableLT` instance can be synthesized or \
            manually provide the field `decidableLT`."
  beq :
      let := ord; BEq α := by
    extract_lets
    first
    | infer_instance
    | exact _root_.BEq.ofOrd _
  beq_iff :
      let := ord; let := le; have := lawfulOrderOrd; let := beq
      ∀ a b : α, a == b ↔ compare a b = .eq := by
    extract_lets
    first
    | exact fun _ _ => Std.compare_eq_eq.symm
    | fail "Failed to automatically derive that `BEq` and `Ord` are compatible. \
            Please ensure that a `LawfulOrderBEq` instance can be synthesized or \
            manually provide the field `beq_iff`."

/--
Use this factory to conveniently define a linear preorder on a type `α` and all the associated
operations and instances given an `Ord α` instance.

Creates a `LinearPreorderPackage α` instance. Such an instance entails `LE α`, `LT α`, `BEq α` and
`Ord α` instances as well as an `IsLinearPreorder α` instance and `LawfulOrder*` instances proving
the compatibility of the operations with the linear preorder.

In the presence of `Ord α` and `TransOrd α` instances, no arguments are required and the factory can
be used as in this example:

```lean
public instance : LinearPreorderPackage X := .ofOrd X
```

If not all of these instances are available via typeclass synthesis, it is necessary to explicitly
provide some arguments:

```lean
public instance : LinearPreorderPackage X := .ofOrd X {
  ord := sorry
  transOrd := sorry }
```

It is also possible to do all of this by hand, without resorting to `LinearPreorderPackage`. This
can be useful if, say, one wants to avoid specifying an `LT α` instance, which is not possible with
`LinearPreorderPackage`.

**How the arguments are filled**

Lean tries to fill all of the fields of the `args : Packages.LinearPreorderOfOrdArgs α` parameter
automatically. If it fails, it is necessary to provide some of the fields manually.

* For the data-carrying typeclasses `LE`, `LT`, `BEq` and `Ord`, existing instances are always
  preferred. If no existing instances can be synthesized, it is attempted to derive an instance from
  the `Ord` instance.
* Some proof obligations can be filled automatically if the data-carrying typeclasses have been
  derived from the `Ord` instance. For example: If the `beq` field is omitted and no `BEq α` instance
  can be synthesized, it is derived from the `Ord α` instance. In this case, `beq_iff`
  can be omitted because Lean can infer that `BEq α` and `Ord α` are compatible.
* Other proof obligations, for example `transOrd`, can be omitted if a matching instance can be
  synthesized.
-/
@[expose, instance_reducible]
public def LinearPreorderPackage.ofOrd (α : Type u)
    (args : Packages.LinearPreorderOfOrdArgs α := by exact {}) : LinearPreorderPackage α :=
  letI := args.ord
  haveI := args.transOrd
  letI := args.le
  haveI := args.lawfulOrderOrd
  { toOrd := args.ord
    toLE := args.le
    toLT := args.lt
    toBEq := args.beq
    toLawfulOrderOrd := args.lawfulOrderOrd
    lt_iff a b := by
      cases h : compare a b
      all_goals simp [h, ← args.lawfulOrderOrd.isLE_compare a _, ← args.lawfulOrderOrd.isGE_compare a _,
        args.lt_iff]
    beq_iff_le_and_ge a b := by
      simp [args.beq_iff, Ordering.eq_eq_iff_isLE_and_isGE, isLE_compare,
        isGE_compare]
    decidableLE := args.decidableLE
    decidableLT := args.decidableLT
    le_refl a := by simp
    le_total a b := by cases h : compare a b <;> simp [h, ← isLE_compare (a := a), ← isGE_compare (a := a)]
    le_trans a b c := by simpa [← isLE_compare] using TransOrd.isLE_trans }

end LinearPreorder

section LinearOrder

namespace FactoryInstances

public scoped instance instMinOfOrd {α : Type u} [Ord α] :
    Min α where
  min a b := if (compare a b).isLE then a else b

public scoped instance instMaxOfOrd {α : Type u} [Ord α] :
    Max α where
  max a b := if (compare b a).isLE then a else b

public instance instLawfulOrderLeftLeaningMinOfOrd {α : Type u} [Ord α] [LE α] [LawfulOrderOrd α] :
    LawfulOrderLeftLeaningMin α where
  min_eq_left a b := by simp +contextual only [← Std.isLE_compare, min, ↑reduceIte, implies_true]
  min_eq_right a b := by
    simp +contextual only [← Std.isLE_compare, min, Bool.false_eq_true, ↑reduceIte, implies_true]

public instance instLawfulOrderLeftLeaningMaxOfOrd {α : Type u} [Ord α] [LE α] [LawfulOrderOrd α] :
    LawfulOrderLeftLeaningMax α where
  max_eq_left a b := by simp +contextual only [← Std.isLE_compare, max, ↑reduceIte, implies_true]
  max_eq_right a b := by
    simp +contextual only [← Std.isLE_compare, max, Bool.false_eq_true, ↑reduceIte, implies_true]

end FactoryInstances

/--
This structure contains all the data needed to create a `LinearOrderPackage α` instance.
Its fields are automatically provided if possible. For the detailed rules how the fields are
inferred, see `LinearOrderPackage.ofOrd`.
-/
public structure Packages.LinearOrderOfOrdArgs (α : Type u) extends
    LinearPreorderOfOrdArgs α where
  eq_of_compare :
      let := ord; let := le
      ∀ a b : α, compare a b = .eq → a = b := by
    extract_lets
    first
    | exact fun _ _ => _root_.Std.LawfulEqOrd.eq_of_compare
    | fail "Failed to derive a `LawfulEqOrd` instance. \
            Please make sure that it can be synthesized or \
            manually provide the field `eq_of_compare`."
  min :
      let := ord
      Min α := by
    extract_lets
    first
    | infer_instance
    | exact _root_.Std.FactoryInstances.instMinOfOrd
  max :
      let := ord
      Max α := by
    extract_lets
    first
    | infer_instance
    | exact _root_.Std.FactoryInstances.instMaxOfOrd
  min_eq :
      let := ord; let := le; let := min; have := lawfulOrderOrd
      ∀ a b : α, Min.min a b = if (compare a b).isLE then a else b := by
    extract_lets
    first
    | exact fun a b => _root_.Std.min_eq_if_isLE_compare (a := a) (b := b)
    | fail "Failed to automatically prove that `min` is left-leaning. \
            Please ensure that a `LawfulOrderLeftLeaningMin` instance can be synthesized or \
            manually provide the field `min_eq`."
  max_eq :
      let := ord; let := le; let := max; have := lawfulOrderOrd
      ∀ a b : α, Max.max a b = if (compare a b).isGE then a else b := by
    extract_lets
    first
    | exact fun a b => _root_.Std.max_eq_if_isGE_compare (a := a) (b := b)
    | fail "Failed to automatically prove that `max` is left-leaning. \
            Please ensure that a `LawfulOrderLeftLeaningMax` instance can be synthesized or \
            manually provide the field `max_eq`."

/--
Use this factory to conveniently define a linear order on a type `α` and all the associated
operations and instances given an `Ord α` instance.

Creates a `LinearOrderPackage α` instance. Such an instance entails `LE α`, `LT α`, `BEq α`,
`Ord α`, `Min α` and `Max α` instances as well as an `IsLinearOrder α` instance and `LawfulOrder*`
instances proving the compatibility of the operations with the linear order.

In the presence of `Ord α`, `TransOrd α` and `LawfulEqOrd α` instances, no arguments are required
and the factory can be used as in this
example:

```lean
public instance : LinearOrderPackage X := .ofLE X
```

If not all of these instances are available via typeclass synthesis, it is necessary to explicitly
provide some arguments:

```lean
public instance : LinearOrderPackage X := .ofLE X {
  transOrd := sorry
  eq_of_compare := sorry }
```

It is also possible to do all of this by hand, without resorting to `LinearOrderPackage`. This
can be useful if, say, one wants to avoid specifying an `LT α` instance, which is not possible with
`LinearOrderPackage`.

**How the arguments are filled**

Lean tries to fill all of the fields of the `args : Packages.LinearOrderOfLEArgs α` parameter
automatically. If it fails, it is necessary to provide some of the fields manually.

* For the data-carrying typeclasses `LE`, `LT`, `BEq`, `Ord`, `Min` and `Max`, existing instances
  are always preferred. If no existing instances can be synthesized, it is attempted to derive an
  instance from the `Ord` instance.
* Some proof obligations can be filled automatically if the data-carrying typeclasses have been
  derived from the `Ord` instance. For example: If the `beq` field is omitted and no `BEq α` instance
  can be synthesized, it is derived from the `LE α` instance. In this case, `beq_iff`
  can be omitted because Lean can infer that `BEq α` and `Ord α` are compatible.
* Other proof obligations, such as `transOrd`, can be omitted if matching instances can be
  synthesized.
-/
@[expose, instance_reducible]
public def LinearOrderPackage.ofOrd (α : Type u)
    (args : Packages.LinearOrderOfOrdArgs α := by exact {}) : LinearOrderPackage α :=
  -- set_option backward.isDefEq.respectTransparency false in
  letI := LinearPreorderPackage.ofOrd α args.toLinearPreorderOfOrdArgs
  haveI : LawfulEqOrd α := ⟨args.eq_of_compare _ _⟩
  letI : Min α := args.min
  letI : Max α := args.max
  { toMin := args.min
    toMax := args.max,
    le_antisymm := Antisymm.antisymm
    toLawfulOrderMin := by
      haveI : LawfulOrderLeftLeaningMin α := .of_eq (by simpa [isLE_compare] using args.min_eq)
      infer_instance
    toLawfulOrderMax := by
      haveI : LawfulOrderLeftLeaningMax α := .of_eq (by simpa [isGE_compare] using args.max_eq)
      infer_instance }

end LinearOrder

end Std
