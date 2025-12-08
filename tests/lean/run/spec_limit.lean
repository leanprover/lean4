/-! This test asserts that the compiler respects compiler.maxRecSpecialize -/

@[specialize, noinline]
def aux2 (f : Nat → Nat) := f 12

/--
error: Exceeded recursive specialization limit (0), consider increasing it with `set_option compiler.maxRecSpecialize 0`
-/
#guard_msgs in
set_option compiler.maxRecSpecialize 0 in
def test := aux2 Nat.succ
