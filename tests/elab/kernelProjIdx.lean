import Lean

/-!
The kernel must reject a projection index that does not fit in the width it is handled at.

`Expr.proj` stores an arbitrary-precision index, and the kernel guarded it with `nat::is_small`,
which admits 63 bits, before narrowing it to `unsigned`. So `.proj P 2^32 p` was silently truncated
into `.proj P 0 p` and accepted — typing and reduction agreed on the wrong field, and the kernel
accepted a term that any checker using arbitrary-precision indices rejects.

`4294967296` is `2^32`, the first index that aliased field `0`; `4294967297` aliased field `1`.

Note that `Expr.proj` indices are 0-based while the pretty printer numbers fields from 1, so the
expected messages below show each index one higher than it was written.
-/

open Lean

structure P where
  a : Nat
  b : Nat

private def p : Expr := mkApp2 (mkConst ``P.mk) (mkRawNatLit 7) (mkRawNatLit 9)

private def kcheck (idx : Nat) : CoreM Unit := do
  let t ← ofExceptKernelException (Kernel.check (← getEnv) {} (mkProj ``P idx p))
  IO.println s!"idx {idx} : {t}"

private def kwhnf (idx : Nat) : CoreM Unit := do
  let r ← ofExceptKernelException (Kernel.whnf (← getEnv) {} (mkProj ``P idx p))
  IO.println s!"idx {idx} ==> {r}"

/-! Controls: in-range indices are unaffected. -/

/-- info: idx 0 : Nat -/
#guard_msgs in
#eval kcheck 0

/-- info: idx 0 ==> 7 -/
#guard_msgs in
#eval kwhnf 0

/-- info: idx 1 ==> 9 -/
#guard_msgs in
#eval kwhnf 1

/-! An index that fits but is out of bounds is rejected, as it always was. -/

/--
error: (kernel) invalid projection
  (P.mk 7 9).3
-/
#guard_msgs in
#eval kcheck 2

/-! An index too wide for `unsigned` is now rejected too, rather than truncated. -/

/--
error: (kernel) invalid projection
  (P.mk 7 9).4294967297
-/
#guard_msgs in
#eval kcheck 4294967296

/-- info: idx 4294967296 ==> (P.mk 7 9).4294967297 -/
#guard_msgs in
#eval kwhnf 4294967296

/-- info: idx 4294967297 ==> (P.mk 7 9).4294967298 -/
#guard_msgs in
#eval kwhnf 4294967297
