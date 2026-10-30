import Lean
/-!
Tests that `lia` proves a cutsat constraint once at the case split where it was stored,
and that the subgoals below the split reuse it (see `Grind.reserveHoistedDecl`).
Each constraint kind (`=`, `≤`, `≠`, `∣`) is used across nested `grind` case splits.
-/
set_option grind.debug true
set_option linter.unusedVariables false

example (x0 x1 x2 x3 : Int) (h0 : x0 = 0 ∨ x0 = 1) (h1 : x1 = 0 ∨ x1 = 1)
    (h2 : x2 = 0 ∨ x2 = 1) (h3 : x3 = 0 ∨ x3 = 1) : x0 + x1 + x2 + x3 ≤ 4 := by
  lia

example (x y z : Int) (h0 : x = 0 ∨ x = 1) (h1 : y = 0 ∨ y = 1) (h2 : z = 0 ∨ z = 1)
    (h3 : x + y ≠ 1) (h4 : y + z ≠ 1) : x = z := by
  lia

example (x y z : Int) (h0 : x = 1 ∨ x = 3) (h1 : y = 0 ∨ y = 2) (h2 : z = 0 ∨ z = 4)
    (h3 : 2 ∣ x + y + z + w) : 2 ∣ w + 1 := by
  lia

example (a b c d : Int) (e1 : a + 2*b - c = 3) (e2 : b - d = 1)
    (h0 : c = 0 ∨ c = 1) (h1 : d = 0 ∨ d = 1) (h2 : a ≤ 0 ∨ a ≥ 10) : a + 2*d ≠ 3 := by
  lia

example (a0 a1 a2 b0 b1 b2 : Nat) : (a0 - b0) + (a1 - b1) + (a2 - b2) ≤ a0 + a1 + a2 := by
  lia

example (y0 y1 y2 a b : Int) (h0 : y0 ≤ 0 ∨ 10 ≤ y0) (h1 : y1 ≤ 0 ∨ 10 ≤ y1)
    (h2 : y2 ≤ 0 ∨ 10 ≤ y2) (h3 : a < b) : a + 1 ≤ b := by
  lia

example (x y : Int) (h0 : x = 0 ∨ x = 1) (h1 : y = 0 ∨ y = 1)
    (h2 : 27 ≤ 11*u + 13*v) (h3 : 11*u + 13*v + x ≤ 45) (h4 : -10 + y ≤ 7*u - 9*v)
    (h5 : 7*u - 9*v ≤ 4) : False := by
  lia

open Lean Meta in
/-- Counts the applications of `declName` in `e`, visiting each shared subterm once. -/
partial def countApps (declName : Name) (e : Expr) : StateT (Std.HashSet UInt64 × Nat) MetaM Unit := do
  let addr := unsafe (ptrAddrUnsafe e).toUInt64
  if (← get).1.contains addr then return
  modify fun (s, n) => (s.insert addr, n)
  match e with
  | .app .. =>
    if e.isAppOf declName then modify fun (s, n) => (s, n + 1)
    countApps declName e.getAppFn
    for a in e.getAppArgs do countApps declName a
  | .lam _ d b _ | .forallE _ d b _ => countApps declName d; countApps declName b
  | .letE _ t v b _ => countApps declName t; countApps declName v; countApps declName b
  | .mdata _ b | .proj _ _ b => countApps declName b
  | _ => pure ()

set_option Elab.async false in
theorem disj6 (x0 x1 x2 x3 x4 x5 : Int) (h0 : x0 = 0 ∨ x0 = 1) (h1 : x1 = 0 ∨ x1 = 1)
    (h2 : x2 = 0 ∨ x2 = 1) (h3 : x3 = 0 ∨ x3 = 1) (h4 : x4 = 0 ∨ x4 = 1)
    (h5 : x5 = 0 ∨ x5 = 1) : x0 + x1 + x2 + x3 + x4 + x5 ≤ 6 := by
  lia

/-
Without sharing, each of the `64` leaves substitutes all `6` variables (`384` steps).
-/
open Lean Meta in
#eval show MetaM Unit from do
  let some (.thmInfo info) := (← getEnv).find? ``disj6._proof_1 | throwError "unknown theorem"
  let ((), (_, n)) ← (countApps ``Int.Internal.Linear.eq_le_subst_nonneg info.value).run ({}, 0)
  unless n < 64 do throwError "unexpected number of substitution steps: {n}"
