import Lean

/-!
This test produces a timeout if we don't use pointer equality at the
kernel infer_type and whnf caches.
Reason: it produces a hash collision for big, very similar, but structurally different terms.
Then, `m_infer_type` cache gets lost comparing terms for equality.
-/

open Lean

def mkDouble (e : Expr) :=
  mkApp2 (mkConst ``Nat.add) e e

def mkDag (e : Expr) : Nat → Expr
  | 0 => e
  | n+1 => mkDouble (mkDouble (mkDag e n))

def foo (a b c d e : Nat) :=
  a + b + c + d + e

open Lean Meta
def mkDef (name : Name) (n : Nat) : MetaM Unit := do
  let type ← mkArrow (mkConst ``Nat) (mkConst ``Nat)
  let big := mkDag (mkBVar 0) n
  let body := mkApp5 (mkConst ``foo) big big big big big
  let value := mkLambda `x .default (mkConst ``Nat) body
  addDecl <| .defnDecl { name, levelParams := [], type, value, safety := .safe, hints := .abbrev }

open Lean Meta
def mkThm (name : Name) (fnName : Name) : MetaM Unit := do
  let type ← mkEq (mkApp (mkConst fnName) (mkNatLit 0)) (mkNatLit 0)
  let value ← mkEqRefl (mkNatLit 0)
  addDecl <| .thmDecl { name, levelParams := [], type, value }

set_option maxRecDepth 10000000

#eval mkDef `test 12000

set_option profiler true
#eval mkThm `testEq `test
