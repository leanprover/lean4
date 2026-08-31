module

/-! Wellfounded recursion should not break under `@[expose] public`. -/

@[expose] public def ackermann : Nat → Nat → Nat
| 0, m => m+1
| n + 1, 0 => ackermann n 1
| n + 1, m + 1 => ackermann n (ackermann (n + 1) m)
termination_by n m => (n,m)

/-- info: ackermann.eq_2 (n : Nat) : ackermann n.succ 0 = ackermann n 1 -/
#guard_msgs in
#check ackermann.eq_2

@[expose] public def foo : Nat → Nat → Nat
| 0, m => m
| n + 1, m => foo n (m+1)
termination_by n m => (n, m)

/-- info: foo.eq_2 (x✝ n : Nat) : foo n.succ x✝ = foo n (x✝ + 1) -/
#guard_msgs in
#check foo.eq_2
