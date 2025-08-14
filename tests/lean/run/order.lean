module

import Init.Data.Order.FactoriesExtra

open Std

variable {α : Type u}

structure X

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
error: could not synthesize default value for field 'lawful_lt' of 'Std.Packages.PreorderOfLEArgs' using tactics
---
error: Failed to automatically prove that the `OrderData` and `LT` instances are compatible.
case refl
α : Type u
inst✝² : LE α
inst✝¹ : DecidableLE α
inst✝ : LT α
this : LE α := inferInstance
⊢ ∀ (a b : α), a < b ↔ a ≤ b ∧ ¬b ≤ a
-/
#guard_msgs in
def packageOfLEOfLT1 [LE α] [DecidableLE α] [LT α] : PreorderPackage α := .ofLE α {
  le_refl := sorry
  le_trans := sorry
}

def packageOfLEOfLT2 [LE α] [DecidableLE α] [LT α] (h : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬ b ≤ a) :
    PreorderPackage α := .ofLE α {
  lawful_lt hi := by cases hi; exact h
  le_refl := sorry
  le_trans := sorry
}
