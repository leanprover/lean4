import Lean

open Lean Meta

/-!
Test: fvar shadowing in nested delayed mvars.

Two delayed mvars bind the same fvar `x_fvar` to different values.
A shared subexpression `succ_x := Nat.succ x_fvar` appears in both scopes.

  ?root    := fun (a : Nat) => ?d1 a
  ?d1      delayed [x_fvar] := ?body
  ?body    := Prod.mk succ_x (?d2 succ_x)     ← succ_x is shared
  ?d2      delayed [x_fvar] := ?inner
  ?inner   := succ_x                            ← same shared object

Expected result:
  fun (a : Nat) => (Nat.succ a, Nat.succ (Nat.succ a))

When resolving ?d1 with arg `a`:
  - succ_x with x_fvar → a  gives  Nat.succ a           (first component)
  - ?d2 gets arg (Nat.succ a), so x_fvar → Nat.succ a
    succ_x with x_fvar → Nat.succ a  gives  Nat.succ (Nat.succ a)  (second component)

A buggy cache could return the cached scope-1 result (Nat.succ a) for the scope-2
visit, producing (Nat.succ a, Nat.succ a) instead.
-/

private def mkShadowTest : MetaM Expr := do
  let nat := mkConst ``Nat
  withLocalDeclD `x nat fun x_fvar => do
    -- shared object referencing x_fvar
    let succ_x := mkApp (mkConst ``Nat.succ) x_fvar

    -- ?inner := succ_x
    let inner ← mkFreshExprMVar nat
    inner.mvarId!.assign succ_x

    -- ?d2 delayed [x_fvar] := ?inner
    let d2_ty ← mkArrow nat nat
    let d2 ← mkFreshExprMVar d2_ty (kind := .syntheticOpaque)
    assignDelayedMVar d2.mvarId! #[x_fvar] inner.mvarId!

    -- ?body := ⟨succ_x, ?d2 succ_x⟩
    let pairTy := mkApp2 (mkConst ``Prod [.succ .zero, .succ .zero]) nat nat
    let body ← mkFreshExprMVar pairTy
    body.mvarId!.assign
      (mkApp4 (mkConst ``Prod.mk [.succ .zero, .succ .zero]) nat nat
        succ_x (mkApp d2 succ_x))

    -- ?d1 delayed [x_fvar] := ?body
    let d1_ty ← mkArrow nat pairTy
    let d1 ← mkFreshExprMVar d1_ty (kind := .syntheticOpaque)
    assignDelayedMVar d1.mvarId! #[x_fvar] body.mvarId!

    -- ?root := fun (a : Nat) => ?d1 a
    let rootTy ← mkArrow nat pairTy
    let root ← mkFreshExprMVar rootTy
    root.mvarId!.assign (Lean.mkLambda `a .default nat (mkApp d1 (.bvar 0)))
    return root

-- Expected: fun (a : Nat) => (Nat.succ a, Nat.succ (Nat.succ a))
private def mkExpected : Expr :=
  let nat := mkConst ``Nat
  let succ := mkConst ``Nat.succ
  -- #0 refers to the lambda-bound `a`
  let succ_a := mkApp succ (.bvar 0)
  let succ_succ_a := mkApp succ succ_a
  let body := mkApp4 (mkConst ``Prod.mk [.succ .zero, .succ .zero]) nat nat succ_a succ_succ_a
  Lean.mkLambda `a .default nat body

run_meta do
  let root ← mkShadowTest
  let result ← instantiateMVars root
  let expected := mkExpected
  unless result == expected do
    throwError "shadow: expected\n  {expected}\ngot\n  {result}"

/-!
Test: an fvar first seen unsubstituted, then substituted at a higher scope.

A shared subexpression `succ_y := Nat.succ y_fvar` is used both:
  - directly in the body of d1 (where y is NOT bound), and
  - inside d2's pending value (where y IS bound).

  ?root   := fun (a : Nat) => ?d1 a
  ?d1     delayed [x] := ?body
  ?body   := Prod.mk succ_y (?d2 succ_y)      ← succ_y shared
  ?d2     delayed [y] := ?inner                ← y is NOW bound
  ?inner  := succ_y                            ← same shared object

Expected result:
  fun (a : Nat) => (Nat.succ y_fvar, Nat.succ (Nat.succ y_fvar))

At scope 1 (d1), x → a. Visit body:
  - succ_y: y is NOT in fvar_subst. Result is succ_y unchanged.
  - ?d2 succ_y: arg succ_y visited → succ_y. Then d2 at scope 2 with y → succ_y.
    - Visit ?inner = succ_y. y IS in fvar_subst → Nat.succ succ_y = Nat.succ (Nat.succ y_fvar).

A buggy cache would return the scope-1 result (succ_y unchanged) at scope 2,
producing (Nat.succ y_fvar, Nat.succ y_fvar) instead.
-/

private def mkLateBindTest : MetaM (Expr × Expr) := do
  let nat := mkConst ``Nat
  withLocalDeclD `x nat fun x_fvar =>
  withLocalDeclD `y nat fun y_fvar => do
    -- shared object referencing y_fvar (NOT x_fvar)
    let succ_y := mkApp (mkConst ``Nat.succ) y_fvar

    -- ?inner := succ_y
    let inner ← mkFreshExprMVar nat
    inner.mvarId!.assign succ_y

    -- ?d2 delayed [y_fvar] := ?inner
    let d2_ty ← mkArrow nat nat
    let d2 ← mkFreshExprMVar d2_ty (kind := .syntheticOpaque)
    assignDelayedMVar d2.mvarId! #[y_fvar] inner.mvarId!

    -- ?body := ⟨succ_y, ?d2 succ_y⟩
    let pairTy := mkApp2 (mkConst ``Prod [.succ .zero, .succ .zero]) nat nat
    let body ← mkFreshExprMVar pairTy
    body.mvarId!.assign
      (mkApp4 (mkConst ``Prod.mk [.succ .zero, .succ .zero]) nat nat
        succ_y (mkApp d2 succ_y))

    -- ?d1 delayed [x_fvar] := ?body
    let d1_ty ← mkArrow nat pairTy
    let d1 ← mkFreshExprMVar d1_ty (kind := .syntheticOpaque)
    assignDelayedMVar d1.mvarId! #[x_fvar] body.mvarId!

    -- ?root := fun (a : Nat) => ?d1 a
    let rootTy ← mkArrow nat pairTy
    let root ← mkFreshExprMVar rootTy
    root.mvarId!.assign (Lean.mkLambda `a .default nat (mkApp d1 (.bvar 0)))
    return (root, y_fvar)

-- Expected: fun (a : Nat) => (Nat.succ y_fvar, Nat.succ (Nat.succ y_fvar))
private def mkExpectedLateBind (y_fvar : Expr) : Expr :=
  let nat := mkConst ``Nat
  let succ := mkConst ``Nat.succ
  let succ_y := mkApp succ y_fvar
  let succ_succ_y := mkApp succ succ_y
  let body := mkApp4 (mkConst ``Prod.mk [.succ .zero, .succ .zero]) nat nat succ_y succ_succ_y
  Lean.mkLambda `a .default nat body

run_meta do
  let (root, y_fvar) ← mkLateBindTest
  let result ← instantiateMVars root
  let expected := mkExpectedLateBind y_fvar
  unless result == expected do
    throwError "late-bind: expected\n  {expected}\ngot\n  {result}"
