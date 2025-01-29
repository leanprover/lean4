opaque n : Nat
@[simp] axiom prio_1000 : n = 1000
@[simp 10] axiom prio_10 : n = 10
-- simp should prefer the prio_1000 lemma with the higher priority
example : n = 1000 := by simp

-- Check that explanation strings are allowed after a priority.
@[simp 1 "really low priority"] axiom prio_1 : n = 1
example : n = 1000 := by simp

#guard_msgs in
-- but that explanation strings are not allowed if there is no priority
@[simp "foo"] axiom foo : 1 = 2
