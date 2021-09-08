import Lean.MetavarContext

open Lean

def check (b : Bool) : IO Unit :=
unless b do throw $ IO.userError "error"

def f := mkConst `f []
def g := mkConst `g []
def a := mkConst `a []
def b := mkConst `b []
def c := mkConst `c []

def b0 := mkBVar 0
def b1 := mkBVar 1
def b2 := mkBVar 2

def u := mkLevelParam `u

def typeE := mkSort levelOne
def natE  := mkConst `Nat []
def boolE := mkConst `Bool []
def vecE  := mkConst `Vec [levelZero]

instance : Coe Name FVarId where
  coe n := { name := n }

instance : Coe Name MVarId where
  coe n := { name := n }

def α := mkFVar `α
def x := mkFVar `x
def y := mkFVar `y
def z := mkFVar `z
def w := mkFVar `w

def m1 := mkMVar `m1
def m2 := mkMVar `m2
def m3 := mkMVar `m3
def m4 := mkMVar `m4
def m5 := mkMVar `m5
def m6 := mkMVar `m6

def bi := BinderInfo.default
def arrow (d b : Expr) := mkForall `_ bi d b
def lctx1 : LocalContext := {}
def lctx2 := lctx1.mkLocalDecl `α `α typeE
def lctx3 := lctx2.mkLocalDecl `x `x natE
def lctx4 := lctx3.mkLocalDecl `y `y α
def lctx5 := lctx4.mkLocalDecl `z `z (mkAppN vecE #[x])
def lctx6 := lctx5.mkLocalDecl `w `w (arrow natE (mkAppN m6 #[α, x, y]))

def t1 := lctx5.mkLambda #[α, x, y] $ mkAppN f #[α, mkAppN g #[x, y], lctx5.mkLambda #[z] (mkApp f z)]
#eval check (!t1.hasFVar)
#eval t1

def mctx1 : MetavarContext := {}
def mctx2  := mctx1.addExprMVarDecl `m1 `m1 lctx3 #[] natE
def mctx3  := mctx2.addExprMVarDecl `m2 `m2 lctx4 #[] α
def mctx4  := mctx3.addExprMVarDecl `m3 `m3 lctx4 #[] natE
def mctx5  := mctx4.addExprMVarDecl `m4 `m4 lctx1 #[] (arrow typeE (arrow natE (arrow α natE)))
def mctx6  := mctx5.addExprMVarDecl `m5 `m5 lctx5 #[] typeE
def mctx7  := mctx5.addExprMVarDecl `m6 `m6 lctx5 #[] (arrow typeE (arrow natE (arrow α natE)))
def mctx8  := mctx7.assignDelayed `m4 lctx4 #[α, x, y] m3
def mctx9  := mctx8.assignExpr `m3 (mkAppN g #[x, y])
def mctx10 := mctx9.assignExpr `m1 a

def t2 := lctx5.mkLambda #[α, x, y] $ mkAppN f #[mkAppN m4 #[α, x, y], x]

#eval check (!t2.hasFVar)
#eval t2
#eval (mctx6.instantiateMVars t2).1
#eval check (!(mctx9.instantiateMVars t2).1.hasMVar)
#eval check (!(mctx9.instantiateMVars t2).1.hasFVar)
#eval (mctx9.instantiateMVars t2).1

-- t3 is ill-formed since m3's localcontext contains ‵α`, `x` and `y`
def t3 := lctx5.mkLambda #[α, x, y] $ mkAppN f #[m3, x]
#eval check (mctx10.instantiateMVars t3).1.hasFVar
#eval (mctx7.instantiateMVars t3).1

partial def mkDiamond : Nat → Expr
| 0     => m1
| (n+1) => mkAppN f #[mkDiamond n, mkDiamond n]

#eval (mctx7.instantiateMVars (mkDiamond 3)).1
#eval (mctx10.instantiateMVars (mkDiamond 3)).1
#eval (mctx7.instantiateMVars (mkDiamond 100)).1.getAppFn
#eval (mctx10.instantiateMVars (mkDiamond 100)).1.getAppFn

def mctx11 := mctx10.assignDelayed `m6 lctx5 #[α, x, y] m5
def mctx12 := mctx11.assignExpr `m5 (arrow α α)

def t4 := lctx6.mkLambda #[α, x, y, w] $ mkAppN f #[mkAppN m4 #[α, x, y], x]

#eval t4
#eval (mctx9.instantiateMVars t4).1
#eval (mctx12.instantiateMVars t4).1
#eval check (mctx9.instantiateMVars t4).1.hasMVar
#eval check (!((mctx9.instantiateMVars t4).1.hasFVar))
#eval check (!(mctx12.instantiateMVars t4).1.hasMVar)
#eval check (!((mctx12.instantiateMVars t4).1.hasFVar))
