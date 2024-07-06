/-!
# Tests of the `decide` tactic
-/

/-!
Success
-/
#guard_msgs in
example : 2 + 2 ≠ 5 := by decide


/-!
False proposition
-/

/--
error: tactic 'decide' proved that the proposition
  1 ≠ 1
is false
-/
#guard_msgs in
example : 1 ≠ 1 := by decide


/-!
Irreducible decidable instance
-/
opaque unknownProp : Prop

/--
error: tactic 'decide' failed for proposition
  unknownProp
since its 'Decidable' instance did not reduce to 'isTrue' or 'isFalse'.

Instead, after unfolding the instance
  Classical.propDecidable
it reduced to
  Classical.choice ⋯

Hint: reduction got stuck on 'Classical.choice', suggesting that there are "classical" instances,
for example due to an 'open scoped Classical' command. The 'decide' tactic works by evaluating a
decision procedure via reduction, but such classical instances cannot be evaluated.
-/
#guard_msgs in
open scoped Classical in
example : unknownProp := by decide


/-!
Reporting unfolded instances and give hint about Eq.rec.
From discussion with Heather Macbeth on Zulip
-/
structure Nice (n : Nat) : Prop :=
  (large : 100 ≤ n)

theorem nice_iff (n : Nat) : Nice n ↔ 100 ≤ n := ⟨Nice.rec id, Nice.mk⟩

def baz (n : Nat) : Decidable (Nice n) := by
  rw [nice_iff]
  infer_instance

instance : Decidable (Nice n) := baz n

/--
error: tactic 'decide' failed for proposition
  Nice 102
since its 'Decidable' instance did not reduce to 'isTrue' or 'isFalse'.

Instead, after unfolding the instances
  instDecidableNice and baz
it reduced to
  ⋯ ▸ inferInstance

Hint: reduction got stuck on '▸' (Eq.rec), which indicates that one of the instances is defined
using tactics such as 'rw' or 'simp'. Use definitions such as 'inferInstanceAs' or
'decidable_of_decidable_of_iff' to change or otherwise "rewrite" the type.
-/
#guard_msgs in
example : Nice 102 := by decide
