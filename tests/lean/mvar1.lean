import Init.Lean.MetavarContext
open Lean

def check (b : Bool) : IO Unit :=
unless b (throw "error")

def f := Expr.const `f []
def g := Expr.const `g []
def a := Expr.const `a []
def b := Expr.const `b []
def c := Expr.const `c []

def b0 := Expr.bvar 0
def b1 := Expr.bvar 1
def b2 := Expr.bvar 2

def u := Level.param `u

def typeE := Expr.sort Level.one
def natE  := Expr.const `Nat []
def boolE := Expr.const `Bool []
def vecE  := Expr.const `Vec [Level.zero]

def α := Expr.fvar `α
def x := Expr.fvar `x
def y := Expr.fvar `y
def z := Expr.fvar `z
def w := Expr.fvar `w

def m1 := Expr.mvar `m1
def m2 := Expr.mvar `m2
def m3 := Expr.mvar `m3
def m4 := Expr.mvar `m4
def m5 := Expr.mvar `m5
def m6 := Expr.mvar `m6

def bi := BinderInfo.default
def arrow (d b : Expr) := Expr.forallE `_ bi d b

def lctx1 : LocalContext := {}
def lctx2 := lctx1.mkLocalDecl `α `α typeE
def lctx3 := lctx2.mkLocalDecl `x `x natE
def lctx4 := lctx3.mkLocalDecl `y `y α
def lctx5 := lctx4.mkLocalDecl `z `z (mkApp vecE #[x])
def lctx6 := lctx5.mkLocalDecl `w `w (arrow natE (mkApp m6 #[α, x, y]))

def t1 := lctx5.mkLambda #[α, x, y] $ mkApp f #[α, mkApp g #[x, y], lctx5.mkLambda #[z] (Expr.app f z)]
#eval check (!t1.hasFVar)
#eval t1

def mctx1 : MetavarContext := {}
def mctx2  := mctx1.mkDecl `m1 `m1 lctx3 natE
def mctx3  := mctx2.mkDecl `m2 `m2 lctx4 α
def mctx4  := mctx3.mkDecl `m3 `m3 lctx4 natE
def mctx5  := mctx4.mkDecl `m4 `m4 lctx1 (arrow typeE (arrow natE (arrow α natE)))
def mctx6  := mctx5.mkDecl `m5 `m5 lctx5 typeE
def mctx7  := mctx5.mkDecl `m6 `m6 lctx5 (arrow typeE (arrow natE (arrow α natE)))
def mctx8  := mctx7.assignDelayed `m4 lctx4 #[α, x, y] m3
def mctx9  := mctx8.assignExpr `m3 (mkApp g #[x, y])
def mctx10 := mctx9.assignExpr `m1 a

def t2 := lctx5.mkLambda #[α, x, y] $ mkApp f #[mkApp m4 #[α, x, y], x]

#eval check (!t2.hasFVar)
#eval t2
#eval (mctx6.instantiateMVars t2).1
#eval check (!(mctx9.instantiateMVars t2).1.hasMVar)
#eval check (!(mctx9.instantiateMVars t2).1.hasFVar)
#eval (mctx9.instantiateMVars t2).1

-- t3 is ill-formed since m3's localcontext contains ‵α`, `x` and `y`
def t3 := lctx5.mkLambda #[α, x, y] $ mkApp f #[m3, x]
#eval check (mctx10.instantiateMVars t3).1.hasFVar
#eval (mctx7.instantiateMVars t3).1

def mkDiamond : Nat → Expr
| 0     => m1
| (n+1) => mkApp f #[mkDiamond n, mkDiamond n]

#eval (mctx7.instantiateMVars (mkDiamond 3)).1
#eval (mctx10.instantiateMVars (mkDiamond 3)).1
#eval (mctx7.instantiateMVars (mkDiamond 100)).1.getAppFn
#eval (mctx10.instantiateMVars (mkDiamond 100)).1.getAppFn

def mctx11 := mctx10.assignDelayed `m6 lctx5 #[α, x, y] m5
def mctx12 := mctx11.assignExpr `m5 (arrow α α)

def t4 := lctx6.mkLambda #[α, x, y, w] $ mkApp f #[mkApp m4 #[α, x, y], x]

#eval t4
#eval (mctx9.instantiateMVars t4).1
#eval (mctx12.instantiateMVars t4).1
#eval check (mctx9.instantiateMVars t4).1.hasMVar
#eval check (!((mctx9.instantiateMVars t4).1.hasFVar))
#eval check (!(mctx12.instantiateMVars t4).1.hasMVar)
#eval check (!((mctx12.instantiateMVars t4).1.hasFVar))
