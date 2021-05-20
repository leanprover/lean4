theorem foo1 (x : Nat) : 0 + x = x := by
  first
   | skip; have : x + x = x + x := rfl; done
          --^ $/lean/plainGoal
   | simp

theorem foo2 (x : Nat) : 0 + x = x := by
  induction x with
  | zero => done
          --^ $/lean/plainGoal
  | succ => done
