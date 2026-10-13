prelude
-- `lake check` re-checks everything in scope, so keep all of `Init` out of it. `lake comparator`
-- also exports the kernel's built-in constants, which need `Nat.gcd` and the bitwise operations.
import Init.Data.Nat.Basic
import Init.Data.Nat.Gcd
import Init.Data.Nat.Bitwise.Basic

/-! A solution every checker `lake check --paranoid` and `lake challenge --paranoid` run accepts. -/

theorem comm (n m : Nat) : n + m = m + n := Nat.add_comm n m
