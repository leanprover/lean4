/-!
Tests for `finish?` in `sym =>` mode (issue #13050).
In `sym =>` mode, `grind`'s entry initialization (proof by contradiction + internalization)
is not applied eagerly, so `finish?` must include the `by_contra` step in the suggested
script for it to be replayable.
-/

/--
info: Try these:
  [apply] by_contra
  [apply] finish only []
-/
#guard_msgs in
example {a b : Nat} (h : a < b) (c : Nat) : a + c < b + c := by
  sym => finish?

-- The suggested script can be replayed
example {a b : Nat} (h : a < b) (c : Nat) : a + c < b + c := by
  sym => by_contra

-- Hypotheses to be introduced are handled by an `intros` step
/--
info: Try these:
  [apply] ⏎
    intros
    by_contra
  [apply] finish only []
-/
#guard_msgs in
example {a b : Nat} (c : Nat) : a < b → a + c < b + c := by
  sym => finish?

-- The suggested script can be replayed
example {a b : Nat} (c : Nat) : a < b → a + c < b + c := by
  sym =>
    intros
    by_contra

/--
info: Try these:
  [apply] ⏎
    by_contra
    lia
  [apply] finish only []
-/
#guard_msgs in
example {a b : Nat} (h : a < b) (c : Nat) : a + c < b + c := by
  sym -order => finish?

/--
info: Try these:
  [apply] ⏎
    intros
    lia
  [apply] finish only []
-/
#guard_msgs in
example {a b : Nat} (h : a < b) (c : Nat) : ¬ a + c < b + c → False := by
  sym -order => finish?

/--
info: Try these:
  [apply] lia
  [apply] finish only []
-/
#guard_msgs in
example {a b : Nat} (h : a < b) (c : Nat) : a + c < b + c := by
  sym -order => by_contra; finish?

-- The suggested script can be replayed
example {a b : Nat} (h : a < b) (c : Nat) : a + c < b + c := by
  sym -order =>
    by_contra
    lia

-- `finish?` in `grind =>` mode is not affected
/--
info: Try these:
  [apply] lia
  [apply] finish only []
-/
#guard_msgs in
example {a b : Nat} (h : a < b) (c : Nat) : a + c < b + c := by
  grind -order => finish?
