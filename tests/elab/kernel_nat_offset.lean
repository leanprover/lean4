/-!
The kernel used to reduce fixed-width arithmetic with a large literal `k` in `k` steps when the other operand is a
variable: `(x + k) % 2^64` compares `2^64` with `x + k` one `Nat.succ` at a time, and `x * k = x * (k - 1) + x` was
reduced by first evaluating `x * (k - 1)`.

The kernel checks `mix.eq_2` and `fnv.eq_2` by first comparing `h` with the argument of the recursive call. This used
to fail with a deep recursion.
-/

def mix : Nat → UInt64 → UInt64
  | 0, h => h
  | n + 1, h => mix n (h + 0x9e3779b97f4a7c15)

example (n : Nat) (h : UInt64) : mix (n + 1) h = mix n (h + 0x9e3779b97f4a7c15) := mix.eq_2 h n

def fnv : Nat → UInt64 → UInt64
  | 0, h => h
  | n + 1, h => fnv n (h * 0x100000001b3)

example (n : Nat) (h : UInt64) : fnv (n + 1) h = fnv n (h * 0x100000001b3) := fnv.eq_2 h n
