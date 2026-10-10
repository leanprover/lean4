/-!
`Nat.ble` and `Nat.beq` remove one `Nat.succ` from both arguments per reduction step, so comparing a literal with
`x + k` used to take `k` steps in `whnf`. Fixed-width arithmetic produces such comparisons: `(x + k) % 2^64` tests
`2^64 ≤ x + k`.
-/

-- #11544: the elaborator used to reach the maximum recursion depth instead of reporting this error.
/--
error: Application type mismatch: The argument
  h
has type
  a = b
but is expected to have type
  (fun x => if x < x + -15 then x else 0) a = (fun x => if x < x + -15 then x else 0) b
in the application
  h ▸ rfl
-/
#guard_msgs in
set_option maxRecDepth 100 in
set_option maxHeartbeats 200 in
theorem crashes (a b : UInt64) (h : a = b) :
    (fun x => if x < x + (-15 : UInt64) then x else 0) a =
    (fun x => if x < x + (-15 : UInt64) then x else 0) b :=
  Eq.ndrec rfl h
