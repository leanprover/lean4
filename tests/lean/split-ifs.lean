/-! Test that the `split` tactic doesn't use `Classical.em` to split ifs.
-/

theorem ifthisthenthat (n : Nat) : (if n = 0 then 0 else 0) = 0 := by split <;> rfl

#print axioms ifthisthenthat
