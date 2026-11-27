module

public import DerivingTest.Instances
public import Lean.Declaration
import all DerivingTest.Handlers -- for the `Secret` type class

public section

/-!
# Tests for the `deriving.*` options
-/

/-!
`deriving.bindersVerbatim` disables instance synthesis but still keeps instance hypotheses
deduplication
-/

set_option deriving.bindersVerbatim true in
structure TestVerbatim (α : Type) (β : Nat → Type) where
  val : Nat
  dup : Nat
  other : β val
  otherDup : β dup
  list : List α
deriving AllGeneralClasses, OtherDataClasses, OtherLawClasses

/--
info: @[instance_reducible, expose] def instToDataTestVerbatimOfNatOfList : {α : Type} →
  {β : Nat → Type} → [ToData Nat] → [(val : Nat) → ToData (β val)] → [ToData (List α)] → ToData (TestVerbatim α β)
-/
#guard_msgs in
#print sig instToDataTestVerbatimOfNatOfList

/-!
`deriving.reduceInstances false` only prevents splitting `MyClass (List α)` into `MyClass α`,
the `MyClass Nat` instance hypothesis is still synthesized.
-/

set_option deriving.reduceInstances false in
structure TestNoReduction (α : Type) (β : Nat → Type) where
  val : Nat
  dup : Nat
  other : β val
  otherDup : β dup
  list : List α
deriving AllGeneralClasses, OtherDataClasses, OtherLawClasses

/--
info: @[instance_reducible, expose] def instToDataTestNoReductionOfList : {α : Type} →
  {β : Nat → Type} → [(val : Nat) → ToData (β val)] → [ToData (List α)] → ToData (TestNoReduction α β)
-/
#guard_msgs in
#print sig instToDataTestNoReductionOfList

/-!
With `deriving.strict` enabled (default), we get errors for missing instances
-/

opaque Missing : Type

/--
error: While deriving an instance for ToData, the following complex instance requirements were encountered that could not be synthesized:
  ToData Missing, reason:
    No matching instances

Hint: You may be able to derive the missing instance using the syntax `deriving instance ClassName for TypeName`.

Hint: If you want to keep these hypotheses as-is, you can disable this error using `set_option deriving.strict false`
-/
#guard_msgs in
structure UsesMissing where
  fine : Nat
  missing : Missing
-- Here and later: We just use `ToData` because the others won't even trigger
deriving ToData

/-!
We also get errors for unsuitable instances
-/

class ToDataExtender (α : Type u) extends ToData α

/--
error: While deriving an instance for ToData, the following complex instance requirements were encountered that could not be synthesized:
  ToData Missing, reason:
    The instance @ToDataExtender.toToData matched but did not have the right shape to be considered

Hint: You may be able to derive the missing instance using the syntax `deriving instance ClassName for TypeName`.

Hint: If you want to keep these hypotheses as-is, you can disable this error using `set_option deriving.strict false`
-/
#guard_msgs in
deriving instance ToData for UsesMissing

/-!
We also get errors for unification failures
-/

structure Any.{u} where
  α : Sort u
  val : α

instance : ToData Any.{0} where
  convert _ := .nat 0

/--
error: While deriving an instance for ToData, the following complex instance requirements were encountered that could not be synthesized:
  ToData Any, reason:
    Failed to unify with the conclusion of instToDataAny

Hint: If you want to keep these hypotheses as-is, you can disable this error using `set_option deriving.strict false`
-/
#guard_msgs in
structure UsesAny1 where
  α : Any.{1}
deriving ToData

/-!
We also get errors for remaining metavariables
-/

inductive SomeType where
  | hi

abbrev Thing (_α : Type) := SomeType

instance : ToData (Thing α) where
  convert _ := .nat 0

/--
error: While deriving an instance for ToData, the following complex instance requirements were encountered that could not be synthesized:
  ToData SomeType, reason:
    After unifying with the conclusion of @instToDataThing, the argument
      ?α
    still contained unexpected metavariables

Hint: If you want to keep these hypotheses as-is, you can disable this error using `set_option deriving.strict false`
-/
#guard_msgs in
structure UsesSomeType where
  type : SomeType
deriving ToData

/-!
We also get errors for duplicate instances
-/

structure Duplicate (α : Type) where

instance [ToData α] : ToData (Duplicate α) where
  convert _ := .nat 0
instance [ToData α] : ToData (Duplicate α) where
  convert _ := .nat 1
instance (priority := low) [ToData α] : ToData (Duplicate α) where
  convert _ := .nat 2

/--
error: While deriving an instance for ToData, the following complex instance requirements were encountered that could not be synthesized:
  ToData (Duplicate α), reason:
    There were multiple instance candidates: @instToDataDuplicate, @instToDataDuplicate_1, and @instToDataDuplicate_2

Hint: Having multiple instance candidates usually indicates that one of the mentioned instances is redundant.
If this is intentional though, you can make the deriving handler choose an instance using `set_option deriving.chooseArbitraryInstance true`.

Hint: If you want to keep these hypotheses as-is, you can disable this error using `set_option deriving.strict false`
-/
#guard_msgs in
structure UsesDuplicate (α : Type) where
  dup : Duplicate α
deriving ToData

/-!
With `deriving.chooseArbitraryInstance`, the deriving handler chooses an instance, in particular,
the last one with the highest priority (similarly to instance synthesis itself).
-/

set_option deriving.chooseArbitraryInstance true in
deriving instance ToData for UsesDuplicate

/-- info: Data.nat 1 -/
#guard_msgs in
#eval ToData.convert { dup := {} : UsesDuplicate Nat }

/-- info: Data.nat 1 -/
#guard_msgs in
#eval ToData.convert { : Duplicate Nat }

/-!
You can disable the errors using `deriving.strict false` to keep the complex hypotheses; but other
hypotheses that were successfully synthesized are not kept, like `MyClass Nat` here.
-/

set_option deriving.strict false in
deriving instance ToData for UsesMissing

/--
info: @[instance_reducible, expose] def instToDataUsesMissingOfMissing : [ToData Missing] → ToData UsesMissing
-/
#guard_msgs in
#print sig instToDataUsesMissingOfMissing

/-!
Even with `deriving.strict false`, missing instances for nested occurrences are still reported.
-/

structure Nestable (α : Type) where
  val : α

/--
error: Error while processing constructor Nested.nest:
  Got stuck at instance requirement for nested type while deriving an instance for ToData:
    ToData (Nestable Nested)
  Reason: The instance @ToDataExtender.toToData matched but did not have the right shape to be considered
-/
#guard_msgs in
inductive Nested where
  | none
  | nest (x : Nestable Nested)
deriving ToData

/-!
With `deriving.implicitBinders false`, the generated instances use explicit binders exactly if they
were explicit in the inductive (otherwise they are always implicit)
-/

set_option deriving.implicitBinders true in -- default
inductive WithImplicit (α : Type) : Nat → Type where
  | thing (x : α) : WithImplicit α 0
deriving AllGeneralClasses, OtherLawClasses

/--
info: @[instance_reducible, expose] def instToDataWithImplicit : {α : Type} →
  [ToData α] → {a : Nat} → ToData (WithImplicit α a)
-/
#guard_msgs in
#print sig instToDataWithImplicit

set_option deriving.implicitBinders false in
inductive WithExplicit (α : Type) : Nat → Type where
  | thing (x : α) : WithExplicit α 0
deriving AllGeneralClasses, OtherLawClasses

/--
info: @[instance_reducible, expose] def instToDataWithExplicit : (α : Type) →
  [ToData α] → (a : Nat) → ToData (WithExplicit α a)
-/
#guard_msgs in
#print sig instToDataWithExplicit

/-!
With `deriving.univPoly true` (default), multiple instances will be generated if needed to cover
all universe possibilities
-/

deriving instance AllGeneralClasses, OtherDataClasses, OtherLawClasses for PSigma

/--
info: @[instance_reducible, expose] def instToDataPSigma.{u, v} : {α : Type u} →
  {β : α → Type v} → [ToData α] → [(fst : α) → ToData (β fst)] → ToData (PSigma β)
-/
#guard_msgs in
#print sig instToDataPSigma
/--
info: @[instance_reducible, expose] def instToDataPSigma_1.{u} : {α : Type u} →
  {β : α → Prop} → [ToData α] → ToData (PSigma β)
-/
#guard_msgs in
#print sig instToDataPSigma_1
/--
info: @[instance_reducible, expose] def instToDataPSigma_2.{v} : {α : Prop} →
  {β : α → Type v} → [(fst : α) → ToData (β fst)] → ToData (PSigma β)
-/
#guard_msgs in
#print sig instToDataPSigma_2
/--
info: @[instance_reducible, expose] def instToDataPSigma_3 : {α : Prop} → {β : α → Prop} → ToData (PSigma β)
-/
#guard_msgs in
#print sig instToDataPSigma_3

/-!
The deriving handler will complain if there are too many possibilities (default limit is 8)
-/

/--
error: Limit set by `deriving.univPoly.limit` exceeded:
Deriving an instance of `ToData` for `ReallyPolymorphic` would require more than 8 different
instantiations of level parameters to be exhaustive, including:
  ReallyPolymorphic.{u + 1, v + 1, w + 1, x + 1}
  ReallyPolymorphic.{u + 1, v + 1, w + 1, 0}
  ReallyPolymorphic.{u + 1, v + 1, 0, x + 1}
  ReallyPolymorphic.{u + 1, v + 1, 0, 0}
  ReallyPolymorphic.{u + 1, 0, w + 1, x + 1}
  ReallyPolymorphic.{u + 1, 0, w + 1, 0}
  ReallyPolymorphic.{u + 1, 0, 0, x + 1}
  ReallyPolymorphic.{u + 1, 0, 0, 0}
  ReallyPolymorphic.{0, v + 1, w + 1, x + 1}
If you just want to generate one instance for the first option, use
`set_option deriving.univPoly false`. If you want to generate instances for all instantiations, use
`set_option deriving.univPoly.limit 0` (note however that this may be quite expensive).
-/
#guard_msgs in
structure ReallyPolymorphic (α : Sort u) (β : Sort v) (γ : Sort w) (δ : Sort x) where
  fst : α
  snd : β
  trd : γ
  fth : δ
deriving ToData

/-!
You can disable the limit with `deriving.univPoly.limit 0`
-/

set_option deriving.univPoly.limit 0 in
deriving instance AllGeneralClasses, OtherDataClasses, OtherLawClasses for ReallyPolymorphic

/--
info: @[instance_reducible, expose] def instToDataReallyPolymorphic_15 : {α β γ δ : Prop} → ToData (ReallyPolymorphic α β γ δ)
-/
#guard_msgs in
#print sig instToDataReallyPolymorphic_15

/-!
`deriving.univPoly false` just causes one instance to be generated
-/

set_option deriving.univPoly false in
deriving instance AllGeneralClasses, OtherDataClasses, OtherLawClasses for Subtype

/--
info: @[instance_reducible, expose] def instToDataSubtype.{u} : {α : Type u} →
  {p : α → Prop} → [ToData α] → ToData (Subtype p)
-/
#guard_msgs in
#print sig instToDataSubtype
/-- error: Unknown constant `instToDataSubtype_1` -/
#guard_msgs in
#print sig instToDataSubtype_1

/-!
The deriving handler also handles nested `Sort`-polymorphic types
-/

inductive NestReallyPolymorphic where
  | none
  | branch
    (self : ReallyPolymorphic NestReallyPolymorphic NestReallyPolymorphic NestReallyPolymorphic
      NestReallyPolymorphic)
deriving AllGeneralClasses, OtherDataClasses

/-!
Because errors may only occur for certain instantiations, errors show the particular instantiation
that caused the failure (if there are multiple). Example: `PropInstMissing` is generated
non-polymorphically and we try to nest it polymorphically
-/

set_option deriving.univPoly false in
structure PropInstMissing (α : Sort u) (β : Sort v) where
  fst : α
  snd : β
deriving ToData

/--
error: For the instantiation `NestPolymorphically.{0}` of level parameters (see option `deriving.univPoly`):
  Error while processing constructor NestPolymorphically.mk:
    Got stuck at instance requirement for nested type while deriving an instance for ToData:
      ToData (PropInstMissing α (NestPolymorphically α))
    Reason: Failed to unify with the conclusion of @instToDataPropInstMissing
-/
#guard_msgs in
structure NestPolymorphically (α : Sort u) where
  inner : PropInstMissing α (NestPolymorphically α)
deriving ToData
