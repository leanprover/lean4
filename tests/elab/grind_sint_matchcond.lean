module

/-!
Tests signed fixed-width literals in hypotheses that resemble match conditions, using both
Grind normalizers. Equivalent spellings must remain connected when a literal wraps, is negated,
or occurs inside a constructor pattern.
-/

set_option grind.debug true
set_option grind.debug.proofs true

inductive Node where
  | mk : Nat → Int8 → Node

example (a : Int8) (h : a = -3 → False) (ha : a = -3) : False := by grind
example (a : Int8) (h : a = 200 → False) (ha : a = -56) : False := by grind
example (a : Int8) (h : a = -0 → False) (ha : a = 0) : False := by grind
example (a : Int8) (h : a = -128 → False) (ha : a = 128) : False := by grind
example (a : Int8) (h : a = -200 → False) (ha : a = 56) : False := by grind
example (a : Int8) (h : a = 255 → False) (ha : a = -1) : False := by grind
example (a : Int8) (h : a = -129 → False) (ha : a = 127) : False := by grind
example (a : Int8) (h : a = -256 → False) (ha : a = 0) : False := by grind
example (a : Int8) (h : a = -257 → False) (ha : a = -1) : False := by grind

example (a : Int16) (h : a = -32768 → False) (ha : a = 32768) : False := by grind
example (a : Int16) (h : a = -32769 → False) (ha : a = 32767) : False := by grind
example (a : Int16) (h : a = -65537 → False) (ha : a = -1) : False := by grind

example (a : Int32) (h : a = -2147483648 → False) (ha : a = 2147483648) : False := by grind
example (a : Int32) (h : a = -2147483649 → False) (ha : a = 2147483647) : False := by grind
example (a : Int32) (h : a = -4294967297 → False) (ha : a = -1) : False := by grind

example (a : Int64) (h : a = -9223372036854775808 → False)
    (ha : a = 9223372036854775808) : False := by grind
example (a : Int64) (h : a = -9223372036854775809 → False)
    (ha : a = 9223372036854775807) : False := by grind
example (a : Int64) (h : a = -18446744073709551617 → False) (ha : a = -1) : False := by grind

example (v : Node) (h : ∀ n, v = Node.mk n (-3) → False)
    (hv : v = Node.mk 0 (-3)) : False := by grind
example (v : Node) (h : ∀ n, v = Node.mk n (-200) → False)
    (hv : v = Node.mk 0 56) : False := by grind
example (v : Node) (h : ∀ n, v = Node.mk n 200 → False)
    (hv : v = Node.mk 0 (-56)) : False := by grind
example (v : Node) (h : ∀ n, v = Node.mk n (-56) → False)
    (hv : v = Node.mk 0 200) : False := by grind

example (a b : Int8) (h : ∀ n : Int8, a = n + 3 → False)
    (ha : a = b + 3) : False := by grind
example (a b : Int8) (h : ∀ n : Int8, a = n + 200 → False)
    (ha : a = b + 200) : False := by grind
example (a b : Int8) (h : ∀ n : Int8, a = n + (-56) → False)
    (ha : a = b + (-56)) : False := by grind
example (a b : Int16) (h : ∀ n : Int16, a = n + 32768 → False)
    (ha : a = b + 32768) : False := by grind
example (a b : Int32) (h : ∀ n : Int32, a = n + 2147483648 → False)
    (ha : a = b + 2147483648) : False := by grind
example (a b : Int64) (h : ∀ n : Int64, a = n + 9223372036854775808 → False)
    (ha : a = b + 9223372036854775808) : False := by grind

set_option backward.grind.normalizer false

example (a : Int8) (h : a = -3 → False) (ha : a = -3) : False := by grind
example (a : Int8) (h : a = 200 → False) (ha : a = -56) : False := by grind
example (a : Int8) (h : a = -0 → False) (ha : a = 0) : False := by grind
example (a : Int8) (h : a = -128 → False) (ha : a = 128) : False := by grind
example (a : Int8) (h : a = -200 → False) (ha : a = 56) : False := by grind
example (a : Int8) (h : a = 255 → False) (ha : a = -1) : False := by grind
example (a : Int8) (h : a = -129 → False) (ha : a = 127) : False := by grind
example (a : Int8) (h : a = -256 → False) (ha : a = 0) : False := by grind
example (a : Int8) (h : a = -257 → False) (ha : a = -1) : False := by grind

example (a : Int16) (h : a = -32768 → False) (ha : a = 32768) : False := by grind
example (a : Int16) (h : a = -32769 → False) (ha : a = 32767) : False := by grind
example (a : Int16) (h : a = -65537 → False) (ha : a = -1) : False := by grind

example (a : Int32) (h : a = -2147483648 → False) (ha : a = 2147483648) : False := by grind
example (a : Int32) (h : a = -2147483649 → False) (ha : a = 2147483647) : False := by grind
example (a : Int32) (h : a = -4294967297 → False) (ha : a = -1) : False := by grind

example (a : Int64) (h : a = -9223372036854775808 → False)
    (ha : a = 9223372036854775808) : False := by grind
example (a : Int64) (h : a = -9223372036854775809 → False)
    (ha : a = 9223372036854775807) : False := by grind
example (a : Int64) (h : a = -18446744073709551617 → False) (ha : a = -1) : False := by grind

example (v : Node) (h : ∀ n, v = Node.mk n (-3) → False)
    (hv : v = Node.mk 0 (-3)) : False := by grind
example (v : Node) (h : ∀ n, v = Node.mk n (-200) → False)
    (hv : v = Node.mk 0 56) : False := by grind
example (v : Node) (h : ∀ n, v = Node.mk n 200 → False)
    (hv : v = Node.mk 0 (-56)) : False := by grind
example (v : Node) (h : ∀ n, v = Node.mk n (-56) → False)
    (hv : v = Node.mk 0 200) : False := by grind

example (a b : Int8) (h : ∀ n : Int8, a = n + 3 → False)
    (ha : a = b + 3) : False := by grind
example (a b : Int8) (h : ∀ n : Int8, a = n + 200 → False)
    (ha : a = b + 200) : False := by grind
example (a b : Int8) (h : ∀ n : Int8, a = n + (-56) → False)
    (ha : a = b + (-56)) : False := by grind
example (a b : Int16) (h : ∀ n : Int16, a = n + 32768 → False)
    (ha : a = b + 32768) : False := by grind
example (a b : Int32) (h : ∀ n : Int32, a = n + 2147483648 → False)
    (ha : a = b + 2147483648) : False := by grind
example (a b : Int64) (h : ∀ n : Int64, a = n + 9223372036854775808 → False)
    (ha : a = b + 9223372036854775808) : False := by grind
