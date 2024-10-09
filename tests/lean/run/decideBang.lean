/-!
# `decide!` tests
-/

/-!
Very basic tests
-/
theorem foo1 : True := by decide
theorem foo2 : True := by decide!

/-!
Tests of the error message when goal is false.
-/

/--
error: tactic 'decide' proved that the proposition
  False
is false
-/
#guard_msgs in
theorem foo3 : False := by decide

/--
error: tactic 'decide!' proved that the proposition
  False
is false
-/
#guard_msgs in
theorem foo4 : False := by decide!

/-!
The kernel sees through irreducible definitions
-/
@[irreducible] def irred {α : Type} (x : α) : α := x

/--
error: tactic 'decide' failed for proposition
  irred 3 = 3
since its 'Decidable' instance
  instDecidableEqNat (irred 3) 3
did not reduce to 'isTrue' or 'isFalse'.

After unfolding the instances 'instDecidableEqNat' and 'Nat.decEq', reduction got stuck at the 'Decidable' instance
  match h : (irred 3).beq 3 with
  | true => isTrue ⋯
  | false => isFalse ⋯
-/
#guard_msgs in theorem gcd_eq1 : irred 3 = 3 := by decide

theorem gcd_eq2 : irred 3 = 3 := by decide!


/-!
The proofs from `decide!` are cached.
-/

theorem thm1 : ∀ x < 100, x * x ≤ 10000 := by decide!

theorem thm1' : ∀ x < 100, x * x ≤ 10000 := by decide!

-- (Note: when run within VS Code, these tests fail since the auxLemmas have a `lean.run` prefix.)
/--
info: theorem thm1 : ∀ (x : Nat), x < 100 → x * x ≤ 10000 :=
decideBang._auxLemma.3
-/
#guard_msgs in #print thm1
/--
info: theorem thm1' : ∀ (x : Nat), x < 100 → x * x ≤ 10000 :=
decideBang._auxLemma.3
-/
#guard_msgs in #print thm1'
