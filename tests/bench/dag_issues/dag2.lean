import Lean

/-!
This test produces a timeout if we don't use pointer equality at the
kernel infer_type and whnf caches.
Reason: it produces a hash collision for big, very similar, but structurally different terms.
Then, `m_infer_type` cache gets lost comparing terms for equality.
-/

open Lean

def f (_a : Nat) : Nat := 0

def mkAdd (a b : Expr) :=
  mkApp2 (mkConst ``Nat.add) a b

def mkTree (d : Nat) (n : Nat) : Expr × Nat :=
  match d with
  | 0   => (mkApp (mkConst ``f) (mkRawNatLit n), n+1)
  | d+1 =>
    let (left, n) := mkTree d n
    let (right, n) := mkTree d n
    (mkAdd left right, n)

def mkDag (e : Expr) (blob : Expr) : Nat → Expr
  | 0 => e
  | n+1 =>
    let a := mkDag e blob n
    mkAdd (mkAdd a blob) a

open Lean Meta
def mkDef (name : Name) (n m : Nat) : MetaM Unit := do
  let type ← mkArrow (mkConst ``Nat) (mkConst ``Nat)
  let (blob, _) := mkTree m 0
  let body      := mkDag (mkBVar 0) blob n
  let value := mkLambda `x .default (mkConst ``Nat) body
  addDecl <| .defnDecl { name, levelParams := [], type, value, safety := .safe, hints := .abbrev }

#eval mkDef `test 5 13

open Lean Meta
def mkThm (name : Name) (fnName : Name) : MetaM Unit := do
  let type ← mkEq (mkApp (mkConst fnName) (mkNatLit 0)) (mkNatLit 0)
  let value ← mkEqRefl (mkNatLit 0)
  addDecl <| .thmDecl { name, levelParams := [], type, value }

set_option maxHeartbeats 1000000

set_option profiler true
example : test 0 = 0 := by
  simp (config := { decide := false, maxSteps := 1000000 }) [test, f]
  done

#exit

example : test 0 = 0 := by
  simp (config := { decide := false, maxSteps := 1000000 }) [test, f]
  done
-- set_option profiler true
-- #eval mkThm `testEq `test



#exit

set_option maxRecDepth 10000000

#eval mkDef `test 12000

set_option profiler true
#eval mkThm `testEq `test
