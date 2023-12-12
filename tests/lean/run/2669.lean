def f : Nat → Nat := fun x => x - x

@[simp] theorem f_zero (n : Nat) : f n = 0 :=
  Nat.sub_self n

example (n : Nat) : False := by
  let g := f n
  have : g + n = n := by
    fail_if_success simp (config := { zeta := false }) [Nat.zero_add] -- Should not succeed
    simp
  sorry

example (h : a = b) : (fun x => a + x) 0 = b := by
  fail_if_success simp (config := { beta := false })
  simp [*]
