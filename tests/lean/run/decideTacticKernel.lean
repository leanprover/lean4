/-!
# `decide +kernel` tests
-/

/-!
Very basic tests
-/
theorem foo1 : True := by decide
theorem foo2 : True := by decide +kernel

/-!
Tests of the error message when goal is false.
-/

/--
error: Tactic `decide` proved that the proposition
  False
is false
-/
#guard_msgs in
theorem foo3 : False := by decide

/--
error: Tactic `decide` proved that the proposition
  False
is false
-/
#guard_msgs in
theorem foo4 : False := by decide +kernel

/-!
The kernel sees through irreducible definitions
-/
@[irreducible] def irred {α : Type} (x : α) : α := x

/--
error: Tactic `decide` failed for proposition
  irred 3 = 3
because its `Decidable` instance
  instDecidableEqNat (irred 3) 3
did not reduce to `isTrue` or `isFalse`.

After unfolding the instances `instDecidableEqNat` and `Nat.decEq`, reduction got stuck at the `Decidable` instance
  match h : (irred 3).beq 3 with
  | true => isTrue ⋯
  | false => isFalse ⋯
-/
#guard_msgs in theorem gcd_eq1 : irred 3 = 3 := by decide

theorem gcd_eq2 : irred 3 = 3 := by decide +kernel


/-!
The proofs from `decide +kernel` are cached.
-/

theorem thm1 : ∀ x < 100, x * x ≤ 10000 := by decide +kernel

theorem thm1' : ∀ x < 100, x * x ≤ 10000 := by decide +kernel

/--
info: theorem thm1 : ∀ (x : Nat), x < 100 → x * x ≤ 10000 :=
thm1._proof_1_1
-/
#guard_msgs in #print thm1
/--
info: theorem thm1' : ∀ (x : Nat), x < 100 → x * x ≤ 10000 :=
thm1'._proof_1_1
-/
#guard_msgs in #print thm1'


/-!
Reverting free variables.
-/

/--
error: Expected type must not contain free variables
  x + 1 ≤ 5

Hint: Use the `+revert` option to automatically clean up and revert free variables
-/
#guard_msgs in
example (x : Nat) (h : x < 5) : x + 1 ≤ 5 := by decide +kernel

example (x : Nat) (h : x < 5) : x + 1 ≤ 5 := by decide +kernel +revert


/--
Can handle universe levels.
-/

instance (p : PUnit.{u} → Prop) [Decidable (p PUnit.unit)] : Decidable (∀ x : PUnit.{u}, p x) :=
  decidable_of_iff (p PUnit.unit) (by constructor; rintro _ ⟨⟩; assumption; intro h; apply h)

example : ∀ (x : PUnit.{u}), x = PUnit.unit := by decide +kernel
