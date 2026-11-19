module

import Lean

/-! Disabled debug assertions validate conditions without changing definitions (#14453). -/

set_option debugAssertions false

def foo : Nat → Nat
  | 0 => 0
  | n + 1 => debug_assert! n ≥ 0; foo n + 1

theorem foo_eq_id (n : Nat) : foo n = n := by
  fun_induction foo n with
  | case1 => rfl
  | case2 n ih => rw [ih]

def h (x : Nat) : Nat := debug_assert! x > 0; x + 1

example (x : Nat) : h x = x + 1 := by unfold h; omega
example (x : Nat) : h x = x + 1 := by rw [h.eq_def]

def acceptsProp (p : Bool × Prop) [Decidable p.2] : Unit :=
  debug_assert! Prod.snd p; ()

def acceptsBool (b : Bool) : Unit := debug_assert! b; ()

def ignoresFalse : Unit := debug_assert! false; ()
example : ignoresFalse = () := rfl

set_option debugAssertions true in
def acceptsEnabledProp (p : Bool × Prop) [Decidable p.2] : Unit :=
  debug_assert! Prod.snd p; ()

def acceptsPropInDo (p : Bool × Prop) [Decidable p.2] : Id Unit := do
  debug_assert! Prod.snd p
  pure ()

example (p : Bool × Prop) [Decidable p.2] : acceptsPropInDo p = () := rfl

def inferredConditionType x := debug_assert! x == x; x + 1
example : inferredConditionType 2 = 3 := rfl
