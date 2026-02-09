namespace Ex1
opaque f : Nat → Nat → Nat

@[simp] theorem foo : f x (x, y).2 = y := by sorry

example : f a b ≤ b := by
  fail_if_success simp -- should fail
  set_option diagnostics true in
  simp (config := { index := false })

end Ex1

namespace Ex2
opaque f : Nat → Nat → Nat

@[simp] theorem foo : f x (no_index (x, y).2) = y := by sorry

example : f a b ≤ b := by
  simp -- should work since `foo` is using `no_index`

end Ex2
