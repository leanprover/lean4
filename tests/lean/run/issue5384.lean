-- A function that reduced badly, as a canary for kernel reduction
def bad (n : Nat) : Nat :=
  if h : n = 0 then 0 else bad (n / 2)
termination_by n

theorem foo : 2 * bad 42000 = bad 42000 + bad 42000 := by simp_arith

theorem foo2 (h : 2 * bad 42000 = bad 42000 + bad 42000 + 1) : False := by simp_arith at h

theorem foo3 (h : bad 42000 + bad 42000 = x) : (2 * bad 42000 = x) := by simp_arith at h; assumption

@[irreducible] def f : Nat → Nat := fun x => x

theorem doesn't_do_anything : f 3 = 3 := by
  fail_if_success simp_arith -- does not apply f_eq and g_eq
  rw [f]
