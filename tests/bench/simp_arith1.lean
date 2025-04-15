import Lean

open Lean Meta Elab in
elab "largeGoal%" : term =>
  let n := 30 -- number of variables
  let r := 3 -- number of repetitions
  let mkAdd := mkApp2 (mkConst ``Nat.add)
  let mkMul := mkApp2 (mkConst ``Nat.mul)
  let decls := Array.ofFn fun (i : Fin n) =>
    ((`x).appendIndexAfter i, (fun _ => pure (mkConst ``Nat)))
  withLocalDeclsD decls fun xs => do
    let mut e₁ : Expr := mkNatLit 42
    let mut e₂ : Expr := mkNatLit 23
    for _ in [:r] do
      for i in [:xs.size] do
        e₁ := mkAdd (mkMul (mkNatLit i) e₁) xs[i]!
        e₂ := mkAdd xs[i]! (mkMul e₂ (mkNatLit (xs.size - i)))
    let goal ← mkEq e₁ e₂
    let goal := mkNot goal
    let goal ← mkForallFVars xs goal
    return goal

set_option maxRecDepth 10000

-- manually verified: most time spent in type-checking
-- set_option trace.profiler true
example : largeGoal% := by
  intros
  simp +arith +decide only
