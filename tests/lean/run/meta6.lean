import Lean.Meta

open Lean
open Lean.Meta

def print (msg : MessageData) : MetaM Unit := do
trace[Meta.debug] msg

def checkM (x : MetaM Bool) : MetaM Unit :=
unless (← x) do throwError "check failed"

def nat   := mkConst `Nat
def boolE := mkConst `Bool
def succ  := mkConst `Nat.succ
def zero  := mkConst `Nat.zero
def add   := mkConst `Nat.add
def io    := mkConst `IO
def type  := mkSort levelOne
def mkArrow (d b : Expr) : Expr := mkForall `_ BinderInfo.default d b

def tst1 : MetaM Unit := do
print "----- tst1 -----";
let m1 ← mkFreshExprMVar (mkArrow nat nat);
let lhs := mkApp m1 zero;
let rhs := zero;
checkM $ fullApproxDefEq $ isDefEq lhs rhs;
pure ()

set_option pp.all true

#eval tst1

set_option trace.Meta.debug true

def tst2 : MetaM Unit := do
print "----- tst2 -----";
let ps ← getParamNames `Or.casesOn; print (toString ps);
let ps ← getParamNames `Iff.rec; print (toString ps);
let ps ← getParamNames `checkM; print (toString ps);
pure ()

#eval tst2

axiom t1 : [Unit] = []
axiom t2 : 0 > 5

def tst3 : MetaM Unit := do
let env ← getEnv;
let t2  ← getConstInfo `t2;
let c   ← mkNoConfusion t2.type (mkConst `t1);
print c;
check c;
let cType ← inferType c;
print cType;
let lt    ← mkLt (mkNatLit 10000000) (mkNatLit 20000000000);
let ltPrf ← mkDecideProof lt;
check ltPrf;
let t ← inferType ltPrf;
print t;
pure ()

#eval tst3

inductive Vec.{u} (α : Type u) : Nat → Type u
| nil            : Vec α 0
| cons {n : Nat} : α → Vec α n → Vec α (n+1)

def tst4 : MetaM Unit :=
withLocalDeclD `x nat fun x =>
withLocalDeclD `y nat fun y => do
let vType ← mkAppM `Vec #[nat, x];
withLocalDeclD `v vType fun v => do
let m ← mkFreshExprSyntheticOpaqueMVar vType;
let subgoals ← caseValues m.mvarId! x.fvarId! #[mkNatLit 2, mkNatLit 3, mkNatLit 5];
subgoals.forM fun s => do {
  print (MessageData.ofGoal s.mvarId);
  assumption s.mvarId
};
let t ← instantiateMVars m;
print t;
check t;
pure ()

#eval tst4

def tst5 : MetaM Unit := do
let arrayNat ← mkAppM `Array #[nat];
withLocalDeclD `a arrayNat fun a => do
withLocalDeclD `b arrayNat fun b => do
let motiveType := _root_.mkArrow arrayNat (mkSort levelZero);
withLocalDeclD `motive motiveType fun motive => do
let mvarType := mkApp motive a;
let mvar ← mkFreshExprSyntheticOpaqueMVar mvarType;
let subgoals ← caseArraySizes mvar.mvarId! a.fvarId! #[1, 0, 4, 5];
subgoals.forM fun s => do {
  print (MessageData.ofGoal s.mvarId);
  pure ()
};
pure ()

set_option trace.Meta.synthInstance false

#eval tst5
