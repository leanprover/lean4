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

def bi := BinderInfo.default
def arrow (d b : Expr) := mkForall `_ bi d b

def lctx1 : LocalContext := {}
def lctx2 := lctx1.mkLocalDecl `α `α typeE
def lctx3 := lctx2.mkLocalDecl `x `x m1
def lctx4 := lctx3.mkLocalDecl `y `y (arrow natE (mkAppN m3 #[α, x]))

def mctx1 : MetavarContext := {}
def mctx2  := mctx1.addExprMVarDecl `m1 `m1 lctx1 #[] typeE
def mctx3  := mctx2.addExprMVarDecl `m2 `m2 lctx3 #[] natE
def mctx4  := mctx3.addExprMVarDecl `m3 `m3 lctx1 #[] (arrow typeE (arrow natE natE))
def mctx5  := mctx4.assignDelayed `m3 lctx3 #[α, x] m2
def mctx6  := mctx5.assignExpr `m2 (arrow α α)
def mctx7  := mctx6.assignExpr `m1 natE

def t2 := lctx4.mkLambda #[α, x, y] $ mkAppN f #[mkAppN m3 #[α, x], x]

#eval check (!t2.hasFVar)
#eval t2
#eval (mctx6.instantiateMVars t2).1
#eval (mctx7.instantiateMVars t2).1
