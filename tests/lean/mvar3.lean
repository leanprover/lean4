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

def bi := BinderInfo.default
def arrow (d b : Expr) := Expr.forallE `_ bi d b

def lctx1 : LocalContext := {}
def lctx2 := lctx1.mkLocalDecl `α `α typeE
def lctx3 := lctx2.mkLocalDecl `x `x m1
def lctx4 := lctx3.mkLocalDecl `y `y (arrow natE m2)

def mctx1 : MetavarContext := {}
def mctx2  := mctx1.mkDecl `m1 `m1 lctx2 typeE
def mctx3  := mctx2.mkDecl `m2 `m2 lctx3 natE
def mctx4  := mctx3.mkDecl `m3 `m3 lctx3 natE
def mctx4' := mctx3.mkDecl `m3 `m3 lctx3 natE true

def R1 :=
match mctx4.mkLambda {namePrefix := `n} lctx4 #[α, x, y] $ mkApp f #[m3, x] with
| Except.ok s    => s
| Except.error e => panic! (toString e)
def e1    := R1.2.2
def mctx5 := R1.1

#eval toString $ mctx5.decls.toList.map Prod.fst
#eval toString mctx5.eAssignment.toList
#eval e1
#eval check (!e1.hasFVar)

def R2 :=
match mctx4'.mkLambda {namePrefix := `n} lctx4 #[α, x, y] $ mkApp f #[m3, x] with
| Except.ok s    => s
| Except.error e => panic! (toString e)
def e2    := R2.2.2
def mctx6 := R2.1

#eval toString $ mctx6.decls.toList.map Prod.fst
#eval toString mctx6.eAssignment.toList
-- ?n.2 was delayed assigned because ?m.3 is synthetic
#eval toString $ mctx6.dAssignment.toList.map Prod.fst
#eval e2
