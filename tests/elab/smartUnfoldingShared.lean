module
import Lean

/-!
Smart unfolding visits the value of `z` to reach the inner match, but should leave the
caller argument `p` intact when it encounters it in `p + n`.
-/

private def f (a p : Nat) : Nat :=
  match a with
  | 0 => 1
  | n+1 =>
    let z := p + n
    match n with
    | 0 => 2
    | m+1 => f m z

open Lean Meta in
run_meta do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
    let a ← mkAppM ``HAdd.hAdd #[x, mkNatLit 3]
    -- Visiting this argument would eliminate its unused `let`.
    let p := mkLet `unused (mkConst ``Nat) (mkNatLit 0) (mkNatLit 7)
    let some r ← unfoldDefinition? (mkApp2 (mkConst ``f) a p) | throwError "expected f to unfold"
    let .letE _ _ v _ _ := r | throwError "expected the let binding for z, got {r}"
    let_expr HAdd.hAdd _ _ _ _ lhs _ := v | throwError "expected an addition, got {v}"
    unless lhs.equal p do throwError "smart unfolding changed the caller argument to {lhs}"

-- Each addition uses its child twice. Reducing the marked leaf must preserve this sharing
-- even when the caller supplies an unfolding predicate.
open Lean Meta in
set_option maxHeartbeats 1000 in
run_meta withCanUnfoldPred canUnfoldDefault do
  let aux := (← getConstInfo (mkSmartUnfoldingNameFor ``f)).value!
  let m := aux.beta #[mkNatLit 0, mkNatLit 0]
  let tree (leaf : Expr) := (14 : Nat).fold (init := leaf) fun _ _ t => mkApp2 (mkConst ``Nat.add) t t
  let some r ← smartUnfoldingReduce? (tree m) | throwError "expected the marked match to reduce"
  unless r.equal (tree (mkNatLit 1)) do throwError "expected every leaf to reduce to 1"

-- Opening a binder instantiates `x` in `x + arg`. Visiting the sum should still skip `arg`.
open Lean Meta in
run_meta do
  let nat := mkConst ``Nat
  let arg := mkLet `unused nat (mkNatLit 0) (mkNatLit 7)
  let sum := mkApp2 (mkConst ``Nat.add) (mkBVar 0) arg
  let inputs := #[mkLambda `x .default nat sum, mkForall `x .default nat (mkApp (mkConst ``Fin) sum),
    mkLet `x nat (mkNatLit 0) sum]
  for e in inputs do
    let some r ← smartUnfoldingReduce? e #[arg] | throwError "expected reduction to succeed"
    unless r.equal e do throwError "expected {e}, got {r}"
