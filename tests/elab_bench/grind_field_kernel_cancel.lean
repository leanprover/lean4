module
public import Lean
public meta import Lean
public meta import Lean.Meta.Sym.Arith.ToExpr

/-!
Benchmark kernel checking of field certificates that cancel an atom and its inverse across a
polynomial. Each declaration checks a fresh certificate without tactic search or elaboration.
-/

open Lean Meta Grind.CommRing

set_option maxHeartbeats 0

run_meta do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let n := if bench then 64 else 8
  let repeats := if bench then 20 else 1
  for i in [:repeats] do
    let terms := (List.range n).foldl (fun (e : Grind.CommRing.Expr) x =>
      e.add ((Grind.CommRing.Expr.num (Int.ofNat (x + i + 1))).mul (.var (x + 2)))) (.num (-1))
    let a := ((Grind.CommRing.Expr.var 0).pow 2 |>.mul (.var 1)).mul terms
    let b := (Grind.CommRing.Expr.var 0).mul terms
    let invs : InvAtoms := [(1, 0)]
    let cert := mkApp3 (mkConst ``Grind.CommRing.Expr.cancelInvs_cert) (toExpr invs) (toExpr a) (toExpr b)
    let type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) cert (mkConst ``Bool.true)
    let value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
    addDecl (.thmDecl { name := ← mkFreshUserName `cancelInv, levelParams := [], type, value })
