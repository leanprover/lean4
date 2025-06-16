open scoped Classical

/--
error: tactic 'native_decide' failed, could not evaluate decidable instance. Error: (interpreter)
unknown declaration 'ohno._nativeDecide_1'
---
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on
'Classical.propDecidable', which is 'noncomputable'
-/
#guard_msgs in
theorem ohno : False := by
  let f : Nat → Nat := fun n => if n=0 then 0 else
    if (∃ k, n = 2 * k) then n / 2 else 3 * n + 1;
  have h2 : f (f 2) ≠ 4 := by
    native_decide;
  have h2 : f (f 2) = 4 := by
    have : ∃ k, 2 = 2 * k := ⟨1, rfl⟩
    simp +decide +arith [f, this];
    omega
  contradiction
