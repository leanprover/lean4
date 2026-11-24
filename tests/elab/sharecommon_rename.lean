import Lean

/-!
Tests that `ShareCommon.shareCommon` maximally shares the subobjects of its argument, that it can be
referred to as `ShareCommon.shareCommon` under `open Lean`, and that the old name is deprecated.
-/

open Lean

def mkPair (n : Nat) : Expr × Expr :=
  (mkApp (mkConst `f) (mkNatLit n), mkApp (mkConst `f) (mkNatLit n))

/-- info: true -/
#guard_msgs in
#eval
  let (a, b) := ShareCommon.shareCommon (mkPair 5)
  unsafe ptrAddrUnsafe a == ptrAddrUnsafe b

/--
warning: `ShareCommon.shareCommon'` has been deprecated: Use `ShareCommon.shareCommon` instead

Hint: Replace the deprecated name:
  ShareCommon.shareCommon'̵
-/
#guard_msgs in
example (e : Expr) : Expr := ShareCommon.shareCommon' e
