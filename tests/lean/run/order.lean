module

import Init.Data.Order.FactoriesExtra

open Std

variable {α : Type u}

structure X

namespace X

#guard_msgs(drop warning) in
opaque instLE : LE X := sorry
attribute [scoped instance] instLE

#guard_msgs(drop warning) in
@[scoped instance] opaque instDecidableLE : DecidableLE X := sorry

#guard_msgs(drop warning) in
@[scoped instance] opaque instTotal : Total (α := X) (· ≤ ·) := sorry

#guard_msgs(drop warning) in
@[scoped instance] opaque instAntisymm : Antisymm (α := X) (· ≤ ·) := sorry

#guard_msgs(drop warning) in
@[scoped instance] opaque instTrans : Trans (α := X) (· ≤ ·) (· ≤ ·) (· ≤ ·) := sorry

scoped instance packageOfLE : LinearOrderPackage X := .ofLE X {
}

example : instLE = (inferInstanceAs (PreorderPackage X)).toLE := rfl
example : IsLinearOrder X := inferInstance
example : LawfulOrderLT X := inferInstance
example : LawfulOrderOrd X := inferInstance
example : LawfulOrderMin X := inferInstance

end X

def packageWithoutSynthesizableInstances : LinearPreorderPackage X := .ofLE X {
  le := X.instLE
  decidableLE := X.instDecidableLE
  le_total := sorry
  le_trans hi a b c := sorry
}

/--
error: could not synthesize default value for field 'lawful_lt' of 'Std.Packages.PreorderOfLEArgs' using tactics
---
error: Failed to automatically prove that the `OrderData` and `LT` instances are compatible.
α : Type u
inst✝² : LE α
inst✝¹ : DecidableLE α
inst✝ : LT α
i : LE α
hi : autoParam (i = inferInstance) _auto✝
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

section

-- instance packageOfLT [LT α] : PreorderPackage α := .ofLT α

-- example [i : LE α] : i = (inferInstanceAs (PreorderPackage α)).toLE := rfl

-- example [LE α] : LawfulOrderLE α := inferInstance
-- example [LE α] : LawfulOrderLT α := inferInstance

end
