constant n : Nat
@[simp] axiom prio_1000 : n = 1000
@[simp 10] axiom prio_10 : n = 10
-- simp should prefer the prio_1000 lemma with the higher priority
example : n = 1000 := by simp
