/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Order.Classes
import Init.Classical

namespace Std

/-!
This module provides utilities for the creation of order-related typeclass instances.
-/

section OfLE

/--
This instance is only publicly defined in `Init.Data.Order.Lemmas`.
-/
instance {r : α → α → Prop} [Total r] : Refl r where
  refl a := by simpa using Total.total a a

/--
If an `LE α` instance is reflexive and transitive, then it represents a preorder.
-/
public theorem IsPreorder.of_le {α : Type u} [LE α]
    (le_refl : Std.Refl (α := α) (· ≤ ·) := by exact inferInstance)
    (le_trans : Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·) := by exact inferInstance) :
    IsPreorder α where
  le_refl := le_refl.refl
  le_trans _ _ _ := le_trans.trans

/--
If an `LE α` instance is transitive and total, then it represents a linear preorder.
-/
public theorem IsLinearPreorder.of_le {α : Type u} [LE α]
    (le_trans : Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·) := by exact inferInstance)
    (le_total : Total (α := α) (· ≤ ·) := by exact inferInstance) :
    IsLinearPreorder α where
  toIsPreorder := .of_le
  le_total := le_total.total

/--
If an `LE α` is reflexive, antisymmetric and transitive, then it represents a partial order.
-/
public theorem IsPartialOrder.of_le {α : Type u} [LE α]
    (le_refl : Std.Refl (α := α) (· ≤ ·) := by exact inferInstance)
    (le_antisymm : Std.Antisymm (α := α) (· ≤ ·) := by exact inferInstance)
    (le_trans : Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·) := by exact inferInstance) :
    IsPartialOrder α where
  toIsPreorder := .of_le
  le_antisymm := le_antisymm.antisymm

/--
If an `LE α` instance is antisymmetric, transitive and total, then it represents a linear order.
-/
public theorem IsLinearOrder.of_le {α : Type u} [LE α]
    (le_antisymm : Std.Antisymm (α := α) (· ≤ ·) := by exact inferInstance)
    (le_trans : Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·) := by exact inferInstance)
    (le_total : Total (α := α) (· ≤ ·) := by exact inferInstance) :
    IsLinearOrder α where
  toIsLinearPreorder := .of_le
  le_antisymm := le_antisymm.antisymm

/--
This lemma derives a `LawfulOrderLT α` instance from a property involving an `LE α` instance.
-/
public theorem LawfulOrderLT.of_le {α : Type u} [LT α] [LE α]
    (lt_iff : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬ b ≤ a) : LawfulOrderLT α where
  lt_iff := lt_iff

/--
This lemma derives a `LawfulOrderBEq α` instance from a property involving an `LE α` instance.
-/
public theorem LawfulOrderBEq.of_le {α : Type u} [BEq α] [LE α]
    (beq_iff : ∀ a b : α, a == b ↔ a ≤ b ∧ b ≤ a) : LawfulOrderBEq α where
  beq_iff_le_and_ge := by simp [beq_iff]

/--
This lemma characterizes in terms of `LE α` when a `Min α` instance "behaves like an infimum
operator".
-/
public theorem LawfulOrderInf.of_le {α : Type u} [Min α] [LE α]
    (le_min_iff : ∀ a b c : α, a ≤ min b c ↔ a ≤ b ∧ a ≤ c) : LawfulOrderInf α where
  le_min_iff := le_min_iff

/--
Returns a `LawfulOrderMin α` instance given certain properties.

This lemma derives a `LawfulOrderMin α` instance from two properties involving `LE α` and `Min α`
instances.

The produced instance entails `LawfulOrderInf α` and `MinEqOr α`.
-/
public theorem LawfulOrderMin.of_le {α : Type u} [Min α] [LE α]
    (le_min_iff : ∀ a b c : α, a ≤ min b c ↔ a ≤ b ∧ a ≤ c)
    (min_eq_or : ∀ a b : α, min a b = a ∨ min a b = b) : LawfulOrderMin α where
  toLawfulOrderInf := .of_le le_min_iff
  toMinEqOr := ⟨min_eq_or⟩

/--
This lemma characterizes in terms of `LE α` when a `Max α` instance "behaves like a supremum
operator".
-/
public def LawfulOrderSup.of_le {α : Type u} [Max α] [LE α]
    (max_le_iff : ∀ a b c : α, max a b ≤ c ↔ a ≤ c ∧ b ≤ c) : LawfulOrderSup α where
  max_le_iff := max_le_iff

/--
Returns a `LawfulOrderMax α` instance given certain properties.

This lemma derives a `LawfulOrderMax α` instance from two properties involving `LE α` and `Max α`
instances.

The produced instance entails `LawfulOrderSup α` and `MaxEqOr α`.
-/
public def LawfulOrderMax.of_le {α : Type u} [Max α] [LE α]
    (max_le_iff : ∀ a b c : α, max a b ≤ c ↔ a ≤ c ∧ b ≤ c)
    (max_eq_or : ∀ a b : α, max a b = a ∨ max a b = b) : LawfulOrderMax α where
  toLawfulOrderSup := .of_le max_le_iff
  toMaxEqOr := ⟨max_eq_or⟩

end OfLE

section OfLT

/--
Creates a *total* `LE α` instance from an `LT α` instance.

This only makes sense for asymmetric `LT α` instances (see `Std.Asymm`).
-/
public def LE.ofLT (α : Type u) [LT α] : LE α where
  le a b := ¬ b < a

/--
The `LE α` instance obtained from an asymmetric `LT α` instance is compatible with said
`LT α` instance.
-/
public instance LawfulOrderLT.of_lt {α : Type u} [LT α] [i : Asymm (α := α) (· < ·)] :
    haveI := LE.ofLT α
    LawfulOrderLT α :=
  letI := LE.ofLT α
  { lt_iff a b := by simpa [LE.ofLT, Classical.not_not] using i.asymm a b }

/--
If an `LT α` instance is asymmetric and its negation is transitive, then `LE.ofLT α` represents a
linear preorder.
-/
public theorem IsLinearPreorder.of_lt {α : Type u} [LT α]
    (lt_asymm : Asymm (α := α) (· < ·) := by exact inferInstance)
    (not_lt_trans : Trans (α := α) (¬ · < ·) (¬ · < ·) (¬ · < ·) := by exact inferInstance) :
    haveI := LE.ofLT α
    IsLinearPreorder α :=
  letI := LE.ofLT α
  { le_trans := by simpa [LE.ofLT] using fun a b c hab hbc => not_lt_trans.trans hbc hab
    le_total a b := by
      apply Or.symm
      open Classical in simpa [LE.ofLT, Decidable.imp_iff_not_or] using lt_asymm.asymm a b
    le_refl a := by
      open Classical in simpa [LE.ofLT] using lt_asymm.asymm a a }

/--
If an `LT α` instance is asymmetric and its negation is transitive and antisymmetric, then
`LE.ofLT α` represents a linear order.
-/
public theorem IsLinearOrder.of_lt {α : Type u} [LT α]
    (lt_asymm : Asymm (α := α) (· < ·) := by exact inferInstance)
    (not_lt_trans : Trans (α := α) (¬ · < ·) (¬ · < ·) (¬ · < ·) := by exact inferInstance)
    (not_lt_antisymm : Antisymm (α := α) (¬ · < ·) := by exact inferInstance) :
    haveI := LE.ofLT α
    IsLinearOrder α :=
  letI := LE.ofLT α
  haveI : IsLinearPreorder α := .of_lt
  { le_antisymm := by
      simpa [LE.ofLT] using fun a b hab hba => not_lt_antisymm.antisymm a b hba hab }

/--
This lemma characterizes in terms of `LT α` when a `Min α` instance
"behaves like an infimum operator" with respect to `LE.ofLT α`.
-/
public theorem LawfulOrderInf.of_lt {α : Type u} [Min α] [LT α]
    (min_lt_iff : ∀ a b c : α, min b c < a ↔ b < a ∨ c < a) :
    haveI := LE.ofLT α
    LawfulOrderInf α :=
  letI := LE.ofLT α
  { le_min_iff a b c := by
      open Classical in
      simp only [LE.ofLT, ← Decidable.not_iff_not (a := ¬ min b c < a)]
      simpa [Decidable.imp_iff_not_or] using min_lt_iff a b c }

/--
Derives a `LawfulOrderMin α` instance for `LE.ofLT` from two properties involving
`LT α` and `Min α` instances.

The produced instance entails `LawfulOrderInf α` and `MinEqOr α`.
-/
public theorem LawfulOrderMin.of_lt {α : Type u} [Min α] [LT α]
    (min_lt_iff : ∀ a b c : α, min b c < a ↔ b < a ∨ c < a)
    (min_eq_or : ∀ a b : α, min a b = a ∨ min a b = b) :
    haveI := LE.ofLT α
    LawfulOrderMin α :=
  letI := LE.ofLT α
  { toLawfulOrderInf := .of_lt min_lt_iff
    toMinEqOr := ⟨min_eq_or⟩ }

/--
This lemma characterizes in terms of `LT α` when a `Max α` instance
"behaves like an supremum operator" with respect to `LE.ofLT α`.
-/
public def LawfulOrderSup.of_lt {α : Type u} [Max α] [LT α]
    (lt_max_iff : ∀ a b c : α, c < max a b ↔ c < a ∨ c < b) :
    haveI := LE.ofLT α
    LawfulOrderSup α :=
  letI := LE.ofLT α
  { max_le_iff a b c := by
      open Classical in
      simp only [LE.ofLT, ← Decidable.not_iff_not ( a := ¬ c < max a b)]
      simpa [Decidable.imp_iff_not_or] using lt_max_iff a b c }

/--
Derives a `LawfulOrderMax α` instance for `LE.ofLT` from two properties involving `LT α` and
`Max α` instances.

The produced instance entails `LawfulOrderSup α` and `MaxEqOr α`.
-/
public def LawfulOrderMax.of_lt {α : Type u} [Max α] [LT α]
    (lt_max_iff : ∀ a b c : α, c < max a b ↔ c < a ∨ c < b)
    (max_eq_or : ∀ a b : α, max a b = a ∨ max a b = b) :
    haveI := LE.ofLT α
    LawfulOrderMax α :=
  letI := LE.ofLT α
  { toLawfulOrderSup := .of_lt lt_max_iff
    toMaxEqOr := ⟨max_eq_or⟩ }

end OfLT

section Packages

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
    LE α, LT α, BEq α, LawfulOrderLT α, LawfulOrderBEq α, IsPreorder α

namespace FactoryInstances

public scoped instance instBEqOfDecidableLE {α : Type u} [LE α] [DecidableLE α] :
    BEq α where
  beq a b := a ≤ b ∧ b ≤ a

public theorem beq_iff {α : Type u} [LE α] [DecidableLE α] {a b : α} :
    a == b ↔ a ≤ b ∧ b ≤ a := by
  simp [BEq.beq]

end FactoryInstances

/--
This structure contains all the data needed to create a `PreorderPackage α` instance. Its fields
are automatically provided if possible. For the detailed rules how the fields are inferred, see
`PreorderPackage.ofLE`.
-/
public structure Packages.PreorderOfLEArgs (α : Type u) where
  le : LE α := by infer_instance
  decidableLE : DecidableLE α := by infer_instance
  lt [i : LE α] (hi : i = le := by rfl) : LT α := by
    first
      | infer_instance
      | exact fun _ => Classical.Order.instLT
  beq [i : LE α] [di : DecidableLE α] (hi : i = le := by rfl) : BEq α := by
    first
      | infer_instance
      | exact fun _ => FactoryInstances.instBEqOfDecidableLE
  lawful_lt [i : LE α] (hi : i = le := by rfl) :
    letI := lt hi; ∀ a b : α, a < b ↔ a ≤ b ∧ ¬ b ≤ a := by
    intro i hi
    first
      | simp only [Classical.Order.instLT, implies_true]; done
      | fail "Failed to automatically prove that the `OrderData` and `LT` instances are compatible."
  lawful_beq [i : LE α] [DecidableLE α] (hi : i = le := by rfl) :
    letI := beq hi; ∀ a b : α, a == b ↔ a ≤ b ∧ b ≤ a := by
    intro i di hi
    first
      | simpa only [FactoryInstances.instBEqOfDecidableLE, BEq.beq] using fun a b =>
          Std.FactoryInstances.beq_iff; done
      | fail "Failed to automatically prove that the `OrderData` and `BEq` instances are compatible."
  le_refl [i : LE α] (hi : i = le := by rfl) : ∀ a : α, a ≤ a := by
    intro i hi
    cases hi
    first
      | exact Std.Refl.refl (r := (· ≤ ·))
      | fail "Failed to automatically prove that the `LE` instance is reflexive."
  le_trans [i : LE α] (hi : i = le := by rfl) :
      ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c := by
    intro i hi
    letI := i
    cases hi
    first
      | exact fun _ _ _ hab hbc => Trans.trans (r := (· ≤ ·)) (s := (· ≤ ·)) (t := (· ≤ ·)) hab hbc
      | fail "Failed to automatically prove that the `LE` instance is transitive."

/--
Use this factory to conveniently define a preorder on a type `α` and all the associated operations
and instances given an `LE α` instance.

Creates a `PreorderPackage α` instance. Such an instance entails `LE α`, `LT α` and
`BEq α` instances as well as an `IsPreorder α` instance an `LawfulOrder*` instances proving the
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
  toLT := letI := args.le; args.lt
  toBEq := letI := args.le; letI := args.decidableLE; args.beq
  toLawfulOrderLT := letI := args.le; letI := args.lt; ⟨args.lawful_lt⟩
  toLawfulOrderBEq := letI := args.le; letI := args.decidableLE; letI := args.beq; ⟨args.lawful_beq⟩
  le_refl := letI := args.le; args.le_refl
  le_trans := letI := args.le; args.le_trans

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
  le_antisymm [i : LE α] (hi : i = le := by rfl) : ∀ a b : α, a ≤ b → b ≤ a → a = b := by
    intro i hi
    letI := i
    cases hi
    first
      | exact Antisymm.antisymm
      | fail "Failed to automatically prove that the `LE` instance is antisymmetric. You can either ensure that an `Asymm` instance is available or manually provide the `le_antisymm` field."

/-
Use this factory to conveniently define a partial order on a type `α` and all the associated
operations and instances given an `LE α` instance.

Creates a `PartialOrderPackage α` instance. Such an instance entails `LE α`, `LT α` and
`BEq α` instances as well as an `IsPartialOrder α` instance an `LawfulOrder*` instances proving the
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
  le_antisymm := letI := args.le; args.le_antisymm

end PartialOrder

end Packages

end Std
