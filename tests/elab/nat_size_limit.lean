import Lean

/-!
Tests the kernel's size limits on the numerals it computes while reducing `Nat`
literals. The limits keep the kernel from spending unbounded memory and time on
giant numerals. The companion `.init.sh` sets `LEAN_NAT_MAX_SIZE=16` so the guards
trip on small inputs; the real defaults are far larger.
-/

open Lean

def kwhnf (a : Name) : CoreM Unit := do
  let env ← getEnv
  let r ← ofExceptKernelException (Kernel.whnf env {} (mkConst a))
  IO.println (toString r)

-- Operands of at most two limbs (<= 16 bytes) are accepted; their three-limb
-- product exceeds the limit and is rejected.
def a : Nat := 18446744073709551616            -- 2^64
def mulOk  : Nat := 4294967296 * 4294967296     -- 2^64, still two limbs
def mulBig : Nat := a * a                        -- 2^128, three limbs

/-- info: 18446744073709551616 -/
#guard_msgs in
#eval kwhnf `mulOk

/-- error: (kernel) the kernel refused a `Nat` numeral because its size exceeds the maximum; increase the LEAN_NAT_MAX_SIZE environment variable to allow it -/
#guard_msgs in
#eval kwhnf `mulBig

-- `Nat.pow`: the result and the exponent are both bounded.
def powBig : Nat := 2 ^ 100
def powHugeExp : Nat := 2 ^ 4294967296

/-- error: (kernel) the kernel refused to evaluate `Nat.pow` because the result would exceed the maximum numeral size; increase the LEAN_NAT_MAX_SIZE environment variable to allow it -/
#guard_msgs in
#eval kwhnf `powBig

/-- error: (kernel) the kernel refused to evaluate `Nat.pow` because its second argument does not fit in a 32-bit unsigned integer -/
#guard_msgs in
#eval kwhnf `powHugeExp

-- `Nat.shiftLeft` result limit.
def shiftBig : Nat := 1 <<< 200

/-- error: (kernel) the kernel refused a `Nat` numeral because its size exceeds the maximum; increase the LEAN_NAT_MAX_SIZE environment variable to allow it -/
#guard_msgs in
#eval kwhnf `shiftBig

-- A numeral entering the kernel directly (source literal) is bounded too.
/-- error: (kernel) the kernel refused a `Nat` numeral because its size exceeds the maximum; increase the LEAN_NAT_MAX_SIZE environment variable to allow it -/
#guard_msgs in
def bigLit : Nat := 340282366920938463463374607431768211456   -- 2^128
