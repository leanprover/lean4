module
public import Lean
public meta import Lean
public meta import Lean.Meta.Sym.Arith.ToExpr

/-!
Check kernel reduction of ring certificate equality on equal and unequal powers, monomials,
and polynomials, including computed monomials and signed coefficients. Exercise the one-pass
addition certificates on interleaved terms and cancellation, with and without a characteristic.
-/

open Lean Meta Grind.CommRing

run_meta do
  let env ← getEnv
  let checkBool (actual : Lean.Expr) (expected : Bool) := do
    unless (← ofExceptKernelException (Kernel.isDefEq env {} actual (toExpr expected))) do
      throwError "incorrect kernel certificate result: {actual}"
  let check (name : Name) (a b : Lean.Expr) (expected : Bool) := do
    checkBool (mkApp2 (mkConst name) a b) expected
  let powers : Array Power := #[⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨1000000, 1000000⟩]
  for a in powers do
    for b in powers do
      check ``Power.beq' (toExpr a) (toExpr b) (a == b)
  let mut mons : Array Mon := #[.unit]
  for a in powers do
    mons := mons.push (.mult a .unit)
    for b in powers do
      mons := mons.push (.mult a (.mult b .unit))
  for a in mons do
    for b in mons do
      check ``Mon.beq' (toExpr a) (toExpr b) (a == b)
  let mut polys : Array Poly := #[]
  for k in #[-1000000, -1, 0, 1, 1000000] do
    polys := polys.push (.num k)
    for m in mons.extract 0 7 do
      polys := polys.push (.add k m (.num 0))
      polys := polys.push (.add 1 m (.add k m (.num (-1))))
  for a in polys do
    for b in polys do
      check ``Poly.beq' (toExpr a) (toExpr b) (a == b)
  for n in [1, 4, 16, 64] do
    let a := (List.range n).foldr (fun x m => Mon.mult ⟨x, x % 3 + 1⟩ m) .unit
    let b := (List.range n).foldr (fun x m => Mon.mult ⟨x, 1⟩ m) .unit
    let product := mkApp2 (mkConst ``Mon.mul_k) (toExpr a) (toExpr b)
    check ``Mon.beq' product (toExpr (a.mul b)) true
    check ``Mon.beq' product (toExpr a) false
  let x := Grind.CommRing.Expr.var 0
  let y := Grind.CommRing.Expr.var 1
  let exprs := #[.num 0, .num (-3), x, y, x.add y, x.sub y, y.sub x,
    (x.add y).pow 2, (x.add y).pow 2 |>.neg]
  for a in exprs do
    for b in exprs do
      let p := a.toPoly
      let q := b.toPoly
      let r := p.combine q
      let cert := mkApp2 (mkConst ``Poly.addEq_k) (toExpr p) (toExpr q)
      checkBool (mkApp cert (toExpr r)) true
      checkBool (mkApp cert (toExpr (r.addConst 1))) false
      for c in [0, 2, 6, 11] do
        let p := a.toPolyC c
        let q := b.toPolyC c
        let r := p.combineC q c
        let cert := mkApp3 (mkConst ``Poly.addEqC_k) (toExpr p) (mkRawNatLit c) (toExpr q)
        checkBool (mkApp cert (toExpr r)) true
        checkBool (mkApp cert (toExpr (r.addConstC 1 c))) false
