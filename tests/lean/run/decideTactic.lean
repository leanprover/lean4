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

After unfolding the instance 'Classical.propDecidable', reduction got stuck at the 'Decidable' instance
  Classical.choice ⋯

Hint: Reduction got stuck on 'Classical.choice', which indicates that a 'Decidable' instance is
defined using classical reasoning, proving an instance exists rather than giving a concrete
construction. The 'decide' tactic works by evaluating a decision procedure via reduction, and it
cannot make progress with such instances. This can occur due to the 'opened scoped Classical'
command, which enables the instance 'Classical.propDecidable'.
-/
#guard_msgs in
open scoped Classical in
example : unknownProp := by decide


/-!
Reporting unfolded instances and give hint about Eq.rec.
From discussion with Heather Macbeth on Zulip
-/
structure Nice (n : Nat) : Prop where
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

After unfolding the instances 'baz' and 'instDecidableNice', reduction got stuck at the 'Decidable' instance
  ⋯ ▸ inferInstance

Hint: Reduction got stuck on '▸' (Eq.rec), which suggests that one of the 'Decidable' instances is
defined using tactics such as 'rw' or 'simp'. To avoid tactics, make use of functions such as
'inferInstanceAs' or 'decidable_of_decidable_of_iff' to alter a proposition.
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

After unfolding the instances 'baz', 'instDecidableNice' and 'instDecidableNot', reduction got stuck
at the 'Decidable' instance
  ⋯ ▸ inferInstance

Hint: Reduction got stuck on '▸' (Eq.rec), which suggests that one of the 'Decidable' instances is
defined using tactics such as 'rw' or 'simp'. To avoid tactics, make use of functions such as
'inferInstanceAs' or 'decidable_of_decidable_of_iff' to alter a proposition.
-/
#guard_msgs in
example : ¬ Nice 102 := by decide


/-!
Reverting free variables.
-/

/--
error: expected type must not contain free variables
  x + 1 ≤ 5
Use the '+revert' option to automatically cleanup and revert free variables.
-/
#guard_msgs in
example (x : Nat) (h : x < 5) : x + 1 ≤ 5 := by decide

example (x : Nat) (h : x < 5) : x + 1 ≤ 5 := by decide +revert


/--
Can handle universe levels.
-/

instance (p : PUnit.{u} → Prop) [Decidable (p PUnit.unit)] : Decidable (∀ x : PUnit.{u}, p x) :=
  decidable_of_iff (p PUnit.unit) (by constructor; rintro _ ⟨⟩; assumption; intro h; apply h)

example : ∀ (x : PUnit.{u}), x = PUnit.unit := by decide
