/-!
Tests that a sort-polymorphic enum-like inductive elaborates (issue #14904).

Such types pass `isEnumType`, but only eliminate into `Prop`, so the auxiliary constructions that
turn a value into data (`.ctorIdx`, `.noConfusion`, the `SizeOf` instance) must be skipped.
-/

set_option bootstrap.inductiveCheckResultingUniverse false

inductive Bool2 : Sort u where
  | true
  | false

/-- info: @Bool2.rec : ∀ {motive : Bool2 → Prop}, motive Bool2.true → motive Bool2.false → ∀ (t : Bool2), motive t -/
#guard_msgs in
#check @Bool2.rec

/-- error: Unknown constant `Bool2.ctorIdx` -/
#guard_msgs in
#check @Bool2.ctorIdx

/-- error: Unknown constant `Bool2.noConfusion` -/
#guard_msgs in
#check @Bool2.noConfusion

/-- error: Unknown constant `Bool2._sizeOf_1` -/
#guard_msgs in
#check @Bool2._sizeOf_1

example : Bool2.true = Bool2.true := rfl
example (x : Bool2) : True := by cases x <;> trivial

-- Single-constructor sort-polymorphic types still eliminate into any `Sort`, so they keep the
-- auxiliary declarations.
inductive Unit2 : Sort u where
  | unit

/-- info: Unit2.ctorIdx : Unit2 → Nat -/
#guard_msgs in
#check @Unit2.ctorIdx

/-- info: @Unit2.noConfusion : {P : Sort u_1} → {x y : Unit2} → x = y → Unit2.noConfusionType P x y -/
#guard_msgs in
#check @Unit2.noConfusion

/-- info: Unit2._sizeOf_1 : Unit2 → Nat -/
#guard_msgs in
#check @Unit2._sizeOf_1
