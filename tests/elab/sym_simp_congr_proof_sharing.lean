module

meta import Lean

/-!
Regression test for #16644. When `Sym.simp` rewrites the index and value in `Array.set`,
only the index equality occurs in the cast of the bounds proof.
-/

open Lean Meta Sym

axiom xs : Array Nat
axiom i : Nat
axiom j : Nat
axiom x : Nat
axiom y : Nat
axiom bounds : i < xs.size
axiom indexEq (_ : Nat → Nat) : i = j
axiom valueEq : x = y

run_meta SymM.run do
  let mkIndexEq (binder : Name) :=
    mkApp (mkConst ``indexEq) (mkLambda binder .default (mkConst ``Nat) (mkBVar 0))
  -- Give the raw index equality a distinct, already shared representative.
  let sharedIndexEq ← shareCommon (mkIndexEq `a)
  let hi := mkIndexEq `b
  let hx := mkConst ``valueEq
  let pre : Sym.Simp.Simproc := fun e => do
    if e.isConstOf ``i then return .step (← share (mkConst ``j)) hi
    if e.isConstOf ``x then return .step (← share (mkConst ``y)) hx
    return .rfl
  let e ← shareCommon <| mkApp5 (mkConst ``Array.set [0]) (mkConst ``Nat)
    (mkConst ``xs) (mkConst ``i) (mkConst ``x) (mkConst ``bounds)
  let .step rhs h .. ← Sym.simp e { pre } | throwError "expected Array.set to be rewritten"
  checkWithKernel h
  unless (rhs.find? (isSameExpr sharedIndexEq)).isSome && (h.find? (isSameExpr sharedIndexEq)).isSome do
    throwError "the RHS and the congruence proof should reuse the shared index equality"
  if ← isMaxShared hx then throwError "the value equality should not be shared"
