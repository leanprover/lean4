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
since its 'Decidable' instance
  Classical.propDecidable unknownProp
did not reduce to 'isTrue' or 'isFalse'.

After unfolding the instance Classical.propDecidable, reduction got stuck at the
'Decidable' instance
  Classical.choice ⋯

Hint: Reduction got stuck on 'Classical.choice', suggesting that there are "classical" instances,
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
since its 'Decidable' instance
  instDecidableNice
did not reduce to 'isTrue' or 'isFalse'.

After unfolding the instances instDecidableNice and baz, reduction got stuck at the
'Decidable' instance
  ⋯ ▸ inferInstance

Hint: Reduction got stuck on '▸' (Eq.rec), which suggests that one of the decidability instances is
defined using tactics such as 'rw' or 'simp'. Use definitions such as 'inferInstanceAs' or
'decidable_of_decidable_of_iff' to alter a proposition.
-/
#guard_msgs in
example : Nice 102 := by decide


/-!
Following `Decidable.rec` to give better messages
-/

/--
error: tactic 'decide' failed for proposition
  ¬Nice 102
since its 'Decidable' instance
  instDecidableNot
did not reduce to 'isTrue' or 'isFalse'.

After unfolding the instances instDecidableNot, instDecidableNice and baz, reduction got stuck
at the 'Decidable' instance
  ⋯ ▸ inferInstance

Hint: Reduction got stuck on '▸' (Eq.rec), which suggests that one of the decidability instances
is defined using tactics such as 'rw' or 'simp'. Use definitions such as 'inferInstanceAs' or
'decidable_of_decidable_of_iff' to alter a proposition.
-/
#guard_msgs in
example : ¬ Nice 102 := by decide
