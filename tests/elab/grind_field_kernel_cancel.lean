module
public import Lean
public meta import Lean
public meta import Lean.Meta.Sym.Arith.ToExpr

/-!
Check recursor-based field inverse cancellation against the native operations, including absent
variables, equal variables, unequal exponents, cancellation to constants, and combined terms.
-/

open Lean Meta Grind.CommRing

run_meta do
  let env ← getEnv
  let check (actual expected : Lean.Expr) := do
    unless (← ofExceptKernelException (Kernel.isDefEq env {} actual expected)) do
      throwError "incorrect kernel cancellation result: {actual}"
  let mut mons : Array Mon := #[.unit, .ofVar 2]
  for a in [0, 1, 2, 5] do
    for b in [0, 1, 2, 5] do
      mons := mons.push (.mult ⟨0, a⟩ (.mult ⟨1, b⟩ .unit))
      mons := mons.push (.mult ⟨0, a⟩ (.mult ⟨1, b⟩ (.ofVar 2)))
  for m in mons do
    for x in [:4] do
      check (mkApp2 (mkConst ``Mon.degreeOf_k) (toExpr m) (mkRawNatLit x))
        (mkRawNatLit (m.degreeOf x))
      check (mkApp2 (mkConst ``Mon.cancelVar_k) (toExpr m) (mkRawNatLit x))
        (toExpr (m.cancelVar x))
      for k in [0, 1, 5] do
        let pw : Power := ⟨x, k⟩
        check (mkApp2 (mkConst ``Mon.mulPow_k) (toExpr pw) (toExpr m))
          (toExpr (m.mulPow pw))
      for y in [:4] do
        check (mkApp3 (mkConst ``Mon.cancelInv_k) (mkRawNatLit x) (mkRawNatLit y) (toExpr m))
          (toExpr (m.cancelInv x y))
  let mut polys : Array Poly := #[.num 0, .num (-3)]
  for k in [-2, 0, 3] do
    for m in mons do
      polys := polys.push (.add k m (.add (-k) (.ofVar 2) (.num 4)))
  for p in polys do
    for invs in [[], [(1, 0)], [(0, 1)], [(0, 0)], [(3, 0)], [(1, 0), (2, 0)]] do
      check (mkApp2 (mkConst ``Poly.cancelInvs_k) (toExpr p) (toExpr (invs : InvAtoms)))
        (toExpr (p.cancelInvs invs))
  let mkQ (q : PolyQ) := mkApp2 (mkConst ``PolyQ.mk) (toExpr q.num) (mkRawNatLit q.den)
  for p in polys.extract 0 12 do
    for invs in [[], [(0, 0)], [(0, 1)], [(0, 2)], [(0, 2), (1, 3)]] do
      for ainvs in [[], [(1, 0)]] do
        check (mkApp3 (mkConst ``Poly.toPolyQ_k) (toExpr p)
          (toExpr (invs : InvVars)) (toExpr (ainvs : InvAtoms)))
          (mkQ (p.toPolyQ invs ainvs))
    for q in polys.extract 0 12 do
      for d in [0, 1, 3] do
        for e in [0, 1, 3] do
          check (mkApp2 (mkConst ``PolyQ.beq') (mkQ ⟨p, d⟩) (mkQ ⟨q, e⟩))
            (toExpr (p == q && d == e))
