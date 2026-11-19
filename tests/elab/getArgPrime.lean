import Lean.Expr

open Lean Expr

example :
  getArg! (mkApp (.mdata .empty (mkApp (mkConst ``Nat.add) (mkNatLit 1))) (mkNatLit 2)) 0
    = mkNatLit 2 := rfl

example :
  getArg!' (mkApp (.mdata .empty (mkApp (mkConst ``Nat.add) (mkNatLit 1))) (mkNatLit 2)) 0
    = mkNatLit 1 := rfl
