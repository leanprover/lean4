open Lean
-- Two DIFFERENT numbers >= 2^64
def n1 := Name.num .anonymous (2^64) -- 18446744073709551616
def n2 := Name.num .anonymous (2^64 + 1) -- 18446744073709551617
-- These are clearly different
#guard (2^64 : Nat) ≠ (2^64 + 1 : Nat) -- passes

/-- info: false -/
#guard_msgs in
#eval Name.beq n1 n2
