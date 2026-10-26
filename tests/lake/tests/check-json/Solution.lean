prelude
-- `lake check` re-checks everything in scope, so keep all of `Init` out of it.
import Init.Data.Nat.Basic

theorem comm (n m : Nat) : n + m = m + n := Nat.add_comm n m
