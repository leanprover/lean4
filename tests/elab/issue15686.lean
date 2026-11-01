import Lean
open Lean

/-!
Regression test for #15686: `Nat` literals that are equal modulo `2^64` must not share one `Expr`
hash. When they did, the kernel check of a list of such literals took quadratic time.
-/

-- `65536 ^ i` is a multiple of `2^64` for `i ≥ 4`.
/-- info: 4000 -/
#guard_msgs in
#eval (Std.HashSet.ofList ((List.range 4000).map fun i => (mkRawNatLit (65536 ^ i)).hash)).size

-- Below `2^64`, the hash is the number itself, also for numbers that are not scalars.
#guard Literal.natHash 12345 == 12345
#guard Literal.natHash (2^63) == (2^63 : Nat).toUInt64
#guard Literal.natHash (2^64 - 1) == (2^64 - 1 : Nat).toUInt64
#guard Literal.natHash (2^64) != Literal.natHash (2^65)
