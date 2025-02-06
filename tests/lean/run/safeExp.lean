/--
warning: exponent 10000000 exceeds the threshold 256, exponentiation operation was not evaluated, use `set_option exponentiation.threshold <num>` to set a new threshold
---
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : 2^2^8000000 = 3^3^10000000 :=
  rfl

/--
-/
#guard_msgs in
set_option exponentiation.threshold 258 in
example : 2^257 = 2*2^256 :=
  rfl

/--
warning: exponent 2008 exceeds the threshold 256, exponentiation operation was not evaluated, use `set_option exponentiation.threshold <num>` to set a new threshold
---
info: k : Nat
h : k = 2008 ^ 2 + 2 ^ 2008
⊢ ((4032064 + 2 ^ 2008) ^ 2 + 2 ^ (4032064 + 2 ^ 2008)) % 10 = 6
---
warning: declaration uses 'sorry'
---
error: (kernel) deep recursion detected
-/
#guard_msgs in
example (k : Nat) (h : k = 2008^2 + 2^2008) : (k^2 + 2^k)%10 = 6 := by
  simp [h]
  trace_state
  sorry

/--
info: k : Nat
h : k = 2008 ^ 2 + 2 ^ 2008
⊢ ((2008 ^ 2 + 2 ^ 2008) ^ 2 + 2 ^ (2008 ^ 2 + 2 ^ 2008)) % 10 = 6
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (k : Nat) (h : k = 2008^2 + 2^2008) : (k^2 + 2^k)%10 = 6 := by
  rw [h]
  trace_state
  sorry
