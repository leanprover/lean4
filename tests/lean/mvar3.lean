import Lean.MetavarContext

open Lean

def mkLambdaTest (mctx : MetavarContext) (ngen : NameGenerator) (lctx : LocalContext) (xs : Array Expr) (e : Expr)
    : Except MetavarContext.MkBinding.Exception (MetavarContext × NameGenerator × Expr) :=
match MetavarContext.mkLambda xs e false true lctx { mctx := mctx, ngen := ngen } with
| EStateM.Result.ok e s    => Except.ok (s.mctx, s.ngen, e)
| EStateM.Result.error e s => Except.error e

def check (b : Bool) : IO Unit :=
unless b do throw $ IO.userError "error"

def f := mkConst `f
def g := mkConst `g
def a := mkConst `a
def b := mkConst `b
def c := mkConst `c

def b0 := mkBVar 0
def b1 := mkBVar 1
def b2 := mkBVar 2

def u := mkLevelParam `u

def typeE := mkSort levelOne
def natE  := mkConst `Nat
def boolE := mkConst `Bool
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
def lctx4 := lctx3.mkLocalDecl `y `y (arrow natE m2)

def mctx1 : MetavarContext := {}
def mctx2  := mctx1.addExprMVarDecl `m1 `m1 lctx2 #[] typeE
def mctx3  := mctx2.addExprMVarDecl `m2 `m2 lctx3 #[] natE
def mctx4  := mctx3.addExprMVarDecl `m3 `m3 lctx3 #[] natE
def mctx4' := mctx3.addExprMVarDecl `m3 `m3 lctx3 #[] natE MetavarKind.syntheticOpaque

def R1 :=
match mkLambdaTest mctx4 {namePrefix := `n} lctx4 #[α, x, y] $ mkAppN f #[m3, x] with
| Except.ok s    => s
| Except.error e => panic! (toString e)
def e1    := R1.2.2
def mctx5 := R1.1

def sortNames (xs : List Name) : List Name :=
(xs.toArray.qsort Name.lt).toList

instance : ToString MVarId where
  toString m := toString m.name

def sortNamePairs {α} [Inhabited α] (xs : List (MVarId × α)) : List (MVarId × α) :=
(xs.toArray.qsort (fun a b => Name.lt a.1.name b.1.name)).toList

#eval toString $ sortNames $ mctx5.decls.toList.map (·.1.name)
#eval toString $ sortNamePairs $ mctx5.eAssignment.toList
#eval e1
#eval check (!e1.hasFVar)

def R2 :=
match mkLambdaTest mctx4' {namePrefix := `n} lctx4 #[α, x, y] $ mkAppN f #[m3, y] with
| Except.ok s    => s
| Except.error e => panic! (toString e)
def e2    := R2.2.2
def mctx6 := R2.1

#eval toString $ sortNames $ mctx6.decls.toList.map (·.1.name)
#eval toString $ sortNamePairs $ mctx6.eAssignment.toList
-- ?n.2 was delayed assigned because ?m.3 is synthetic
#eval toString $ sortNames $ mctx6.dAssignment.toList.map (·.1.name)
#eval e2

#print "assigning ?m1 and ?n.1"
def R3 :=
let mctx := mctx6.assignExpr `m3 x;
let mctx := mctx.assignExpr (Name.mkNum `n 1) (mkLambda `_ bi typeE natE);
-- ?n.2 is instantiated because we have the delayed assignment `?n.2 α x := ?m1`
(mctx.instantiateMVars e2)
def e3    := R3.1
def mctx7 := R3.2
#eval e3
