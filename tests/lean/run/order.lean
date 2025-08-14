
import Init.Data.Order.PackageFactories

open Std

variable {α : Type u}

opaque X : Type := Unit

namespace X

#guard_msgs(error, drop warning) in
opaque instLE : LE X := sorry
attribute [scoped instance] instLE

#guard_msgs(error, drop warning) in
@[scoped instance] opaque instDecidableLE : DecidableLE X := sorry

#guard_msgs(error, drop warning) in
@[instance] opaque instTotal : Total (α := X) (· ≤ ·) := sorry

#guard_msgs(error, drop warning) in
@[instance] opaque instAntisymm : Antisymm (α := X) (· ≤ ·) := sorry

#guard_msgs(error, drop warning) in
@[instance] opaque instTrans : Trans (α := X) (· ≤ ·) (· ≤ ·) (· ≤ ·) := sorry

namespace Package

scoped instance packageOfLE : LinearOrderPackage X := .ofLE X

example : instLE = (inferInstanceAs (PreorderPackage X)).toLE := rfl
example : IsLinearOrder X := inferInstance
example : LawfulOrderLT X := inferInstance
example : LawfulOrderOrd X := inferInstance
example : LawfulOrderMin X := inferInstance
example : LawfulOrderMax X := inferInstance
example : LawfulOrderLeftLeaningMin X := inferInstance
example : LawfulOrderLeftLeaningMax X := inferInstance

end Package

end X

section

def packageWithoutSynthesizableInstances : LinearOrderPackage X := .ofLE X {
  le := X.instLE
  decidableLE := X.instDecidableLE }

end

section

attribute [local instance] X.Package.packageOfLE

def packageWithoutSynthesizableInstances' : LinearOrderPackage X := .ofLE X {
  le := X.instLE
  decidableLE := X.instDecidableLE
}

end

/--
error: could not synthesize default value for field 'lt_iff' of 'Std.Packages.PreorderOfLEArgs' using tactics
---
error: Failed to automatically prove that the `LE` and `LT` instances are compatible. Please ensure that a `LawfulOrderLT` instance can be synthesized or manually provide the field `lt_iff`.
α : Type u
inst✝² : LE α
inst✝¹ : DecidableLE α
inst✝ : LT α
this✝¹ : LE α := inferInstance
this✝ : LT α := inferInstance
⊢ ∀ (a b : α), a < b ↔ a ≤ b ∧ ¬b ≤ a
-/
#guard_msgs in
def packageOfLEOfLT1 [LE α] [DecidableLE α] [LT α] : PreorderPackage α := .ofLE α {
  le_refl := sorry
  le_trans := sorry
}

def packageOfLEOfLT2 [LE α] [DecidableLE α] [LT α] (h : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬ b ≤ a) :
    PreorderPackage α := .ofLE α {
  lt_iff := h
  le_refl := sorry
  le_trans := sorry
}

namespace OrdTests

section

#guard_msgs(error, drop warning) in
opaque _root_.X.instOrd : Ord X := sorry

def packageWithoutSynthesizableInstances : Packages.LinearPreorderOfOrdArgs X := {
  ord := X.instOrd
  transOrd := sorry
}

end

end OrdTests
