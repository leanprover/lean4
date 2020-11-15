inductive bvar : Type
  | mk (n : Nat)

def bvar_eq : bvar → bvar → Bool
  | bvar.mk n1, bvar.mk n2 => n1=n2

inductive bExpr : Type
  | BLit (b: Bool)
  | BVar (v: bvar)

def benv := bvar → Bool

def bEval : bExpr → benv → Bool
  | bExpr.BLit b, i => b
  | bExpr.BVar v, i => i v

def init_benv : benv := λ v => false

def update_benv : benv → bvar → Bool → benv
  | i, v, b => λ v2 => if (bvar_eq v v2) then b else (i v2)

inductive bCmd : Type
  | bAssm (v : bvar) (e : bExpr)
  | bSeq (c1 c2 : bCmd)

-- Unlike Lean 3, we can have nested match-expressions and still use structural recursion
def cEval : benv → bCmd → benv
| i0, c => match c with
  | bCmd.bAssm v e  => update_benv i0 v (bEval e i0)
  | bCmd.bSeq c1 c2 =>
    let i1 := cEval i0 c1
    cEval i1 c2

def myFirstProg := bCmd.bAssm (bvar.mk 0) (bExpr.BLit false)

def newEnv :=
  cEval init_benv myFirstProg

#eval newEnv (bvar.mk 0)
