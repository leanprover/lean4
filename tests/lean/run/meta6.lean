import Lean.Meta
new_frontend
open Lean
open Lean.Meta

def print (msg : MessageData) : MetaM Unit :=
trace! `Meta.debug msg

def check (x : MetaM Bool) : MetaM Unit :=
unlessM x $ throwError "check failed"

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
m1 ← mkFreshExprMVar (mkArrow nat nat);
let lhs := mkApp m1 zero;
let rhs := zero;
check $ fullApproxDefEq $ isDefEq lhs rhs;
pure ()

set_option pp.all true

#eval tst1

set_option trace.Meta.debug true

def tst2 : MetaM Unit := do
print "----- tst2 -----";
ps ← getParamNames `Or.elim; print (toString ps);
ps ← getParamNames `Iff.elim; print (toString ps);
ps ← getParamNames `check; print (toString ps);
pure ()

#eval tst2

axiom t1 : [Unit] = []
axiom t2 : 0 > 5

def tst3 : MetaM Unit := do
env ← getEnv;
t2  ← getConstInfo `t2;
c   ← mkNoConfusion t2.type (mkConst `t1);
print c;
Meta.check c;
cType ← inferType c;
print cType;
lt    ← mkLt (mkNatLit 10000000) (mkNatLit 20000000000);
ltPrf ← mkDecideProof lt;
Meta.check ltPrf;
t ← inferType ltPrf;
print t;
pure ()

#eval tst3

inductive Vec.{u} (α : Type u) : Nat → Type u
| nil            : Vec α 0
| cons {n : Nat} : α → Vec α n → Vec α (n+1)

def tst4 : MetaM Unit :=
withLocalDeclD `x nat fun x =>
withLocalDeclD `y nat fun y => do
vType ← mkAppM `Vec #[nat, x];
withLocalDeclD `v vType fun v => do
m ← mkFreshExprSyntheticOpaqueMVar vType;
subgoals ← caseValues m.mvarId! x.fvarId! #[mkNatLit 2, mkNatLit 3, mkNatLit 5];
subgoals.forM fun s => do {
  print (MessageData.ofGoal s.mvarId);
  assumption s.mvarId
};
t ← instantiateMVars m;
print t;
Meta.check t;
pure ()

#eval tst4

def tst5 : MetaM Unit := do
arrayNat ← mkAppM `Array #[nat];
withLocalDeclD `a arrayNat fun a => do
withLocalDeclD `b arrayNat fun b => do
let motiveType := mkArrow arrayNat (mkSort levelZero);
withLocalDeclD `motive motiveType fun motive => do
let mvarType := mkApp motive a;
mvar ← mkFreshExprSyntheticOpaqueMVar mvarType;
subgoals ← caseArraySizes mvar.mvarId! a.fvarId! #[1, 0, 4, 5];
subgoals.forM fun s => do {
  print (MessageData.ofGoal s.mvarId);
  pure ()
};
pure ()

set_option trace.Meta.synthInstance false

#eval tst5
