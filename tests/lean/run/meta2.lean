import Lean.Meta
open Lean
open Lean.Meta

set_option pp.mvars false

-- set_option trace.Meta true
--set_option trace.Meta.isDefEq.step false
-- set_option trace.Meta.isDefEq.delta false
set_option trace.Meta.debug true

def print (msg : MessageData) : MetaM Unit := do
trace[Meta.debug] msg

def checkM (x : MetaM Bool) : MetaM Unit :=
unless (← x) do throwError "check failed"

def getAssignment (m : Expr) : MetaM Expr :=
do let v? ← getExprMVarAssignment? m.mvarId!;
   (match v? with
   | some v => pure v
   | none   => throwError "metavariable is not assigned")

def nat   := mkConst `Nat
def boolE := mkConst `Bool
def succ  := mkConst `Nat.succ
def zero  := mkConst `Nat.zero
def add   := mkConst `Nat.add
def io    := mkConst `IO
def type  := mkSort levelOne
def boolFalse := mkConst `Bool.false
def boolTrue := mkConst `Bool.true

def tst1 : MetaM Unit :=
do print "----- tst1 -----";
   let mvar <- mkFreshExprMVar nat;
   checkM $ isExprDefEq mvar (mkNatLit 10);
   checkM $ isExprDefEq mvar (mkNatLit 10);
   pure ()

/-- info: [Meta.debug] ----- tst1 ----- -/
#guard_msgs in
#eval tst1

def tst2 : MetaM Unit :=
do print "----- tst2 -----";
   let mvar <- mkFreshExprMVar nat;
   checkM $ isExprDefEq (mkApp succ mvar) (mkApp succ (mkNatLit 10));
   checkM $ isExprDefEq mvar (mkNatLit 10);
   pure ()

/-- info: [Meta.debug] ----- tst2 ----- -/
#guard_msgs in
#eval tst2

def tst3 : MetaM Unit :=
do print "----- tst3 -----";
   let t   := mkLambda `x BinderInfo.default nat $ mkBVar 0;
   let mvar ← mkFreshExprMVar (mkForall `x BinderInfo.default nat nat);
   lambdaTelescope t fun xs _ => do
     let x := xs[0]!
     checkM $ isExprDefEq (mkApp mvar x) (mkAppN add #[x, mkAppN add #[mkNatLit 10, x]]);
     pure ();
   let v ← getAssignment mvar;
   print v;
   pure ()

/--
info: [Meta.debug] ----- tst3 -----
[Meta.debug] fun x => x.add (Nat.add 10 x)
-/
#guard_msgs in
#eval tst3

def tst4 : MetaM Unit :=
do print "----- tst4 -----";
   let t   := mkLambda `x BinderInfo.default nat $ mkBVar 0;
   lambdaTelescope t fun xs _ => do
     let x := xs[0]!
     let mvar ← mkFreshExprMVar (mkForall `x BinderInfo.default nat nat);
     -- the following `isExprDefEq` fails because `x` is also in the context of `mvar`
     checkM $ not <$> isExprDefEq (mkApp mvar x) (mkAppN add #[x, mkAppN add #[mkNatLit 10, x]]);
     checkM $ approxDefEq $ isExprDefEq (mkApp mvar x) (mkAppN add #[x, mkAppN add #[mkNatLit 10, x]]);
     let v ← getAssignment mvar;
     print v;
     pure ();
   pure ()

/--
info: [Meta.debug] ----- tst4 -----
[Meta.debug] fun x => x.add (Nat.add 10 x)
-/
#guard_msgs in
#eval tst4

def mkAppC (c : Name) (xs : Array Expr) : MetaM Expr :=
do let r ← mkAppM c xs;
   check r;
   pure r

def mkProd (a b : Expr) : MetaM Expr := mkAppC `Prod #[a, b]
def mkPair (a b : Expr) : MetaM Expr := mkAppC `Prod.mk #[a, b]
def mkFst (s : Expr) : MetaM Expr := mkAppC `Prod.fst #[s]
def mkSnd (s : Expr) : MetaM Expr := mkAppC `Prod.snd #[s]

def tst5 : MetaM Unit :=
do print "----- tst5 -----";
   let p₁ ← mkPair (mkNatLit 1) (mkNatLit 2);
   let x  ← mkFst p₁;
   print x;
   let v  ← whnf x;
   print v;
   let v  ← withTransparency TransparencyMode.reducible $ whnf x;
   print v;
   let x  ← mkId x;
   print x;
   let prod ← mkProd nat nat;
   let m ← mkFreshExprMVar prod;
   let y ← mkFst m;
   checkM $ isExprDefEq y x;
   print y;
   let x ← mkProjection p₁ `fst;
   print x;
   let y ← mkProjection p₁ `snd;
   print y

/--
info: [Meta.debug] ----- tst5 -----
[Meta.debug] (1, 2).fst
[Meta.debug] 1
[Meta.debug] 1
[Meta.debug] id (1, 2).fst
[Meta.debug] (1, 2).fst
[Meta.debug] (1, 2).fst
[Meta.debug] (1, 2).snd
-/
#guard_msgs in
#eval tst5

def tst6 : MetaM Unit :=
do print "----- tst6 -----";
   withLocalDeclD `x nat $ fun x => do
     let m ← mkFreshExprMVar nat;
     let t := mkAppN add #[m, mkNatLit 4];
     let s := mkAppN add #[x, mkNatLit 3];
     checkM $ not <$> isExprDefEq t s;
     let s := mkAppN add #[x, mkNatLit 6];
     checkM $ isExprDefEq t s;
     let v ← getAssignment m;
     checkM $ pure $ v == (← mkAdd x (mkNatLit 2))
     print v;
     let m ← mkFreshExprMVar nat;
     let t := mkAppN add #[m, mkNatLit 4];
     let s := mkNatLit 3;
     checkM $ not <$> isExprDefEq t s;
     let s := mkNatLit 10;
     checkM $ isExprDefEq t s;
     let v ← getAssignment m;
     checkM $ pure $ v == mkNatLit 6;
     print v;
     pure ()

/--
info: [Meta.debug] ----- tst6 -----
[Meta.debug] x + 2
[Meta.debug] 6
-/
#guard_msgs in
#eval tst6

def tst7 : MetaM Unit :=
do print "----- tst7 -----";
   withLocalDeclD `x type $ fun x => do
     let m1 ← mkFreshExprMVar (← mkArrow type type);
     let m2 ← mkFreshExprMVar type;
     let t := mkApp io x;
     -- we need to use foApprox to solve `?m1 ?m2 =?= IO x`
     checkM $ not <$> isDefEq (mkApp m1 m2) t;
     checkM $ approxDefEq $ isDefEq (mkApp m1 m2) t;
     let v ← getAssignment m1;
     checkM $ pure $ v == io;
     let v ← getAssignment m2;
     checkM $ pure $ v == x;
     pure ()

/--
error: check failed
---
info: [Meta.debug] ----- tst7 -----
-/
#guard_msgs in
#eval tst7

def tst9 : MetaM Unit :=
do print "----- tst9 -----";
   let env ← getEnv;
   print (toString (← isReducible `Prod.fst))
   print (toString (← isReducible `Add.add))
   pure ()

/--
info: [Meta.debug] ----- tst9 -----
[Meta.debug] true
[Meta.debug] false
-/
#guard_msgs in
#eval tst9

def tst10 : MetaM Unit :=
do print "----- tst10 -----";
   let t ← withLocalDeclD `x nat $ fun x => do {
     let b := mkAppN add #[x, mkAppN add #[mkNatLit 2, mkNatLit 3]];
     mkLambdaFVars #[x] b
   };
   print t;
   let t ← reduce t;
   print t;
   pure ()

/--
info: [Meta.debug] ----- tst10 -----
[Meta.debug] fun x => x.add (Nat.add 2 3)
[Meta.debug] fun x => x.succ.succ.succ.succ.succ
-/
#guard_msgs in
#eval tst10

def tst11 : MetaM Unit :=
do print "----- tst11 -----";
   checkM $ isType nat;
   checkM $ isType (← mkArrow nat nat);
   checkM $ not <$> isType add;
   checkM $ not <$> isType (mkNatLit 1);
   withLocalDeclD `x nat fun x => do
     checkM $ not <$> isType x;
     checkM $ not <$> (mkLambdaFVars #[x] x >>= isType);
     checkM $ not <$> (mkLambdaFVars #[x] nat >>= isType);
     let t ← mkEq x (mkNatLit 0);
     let t ← mkForallFVars #[x] t (usedOnly := true);
     print t;
     checkM $ isType t;
     pure ();
   pure ()

/--
info: [Meta.debug] ----- tst11 -----
[Meta.debug] ∀ (x : Nat), x = 0
-/
#guard_msgs in
#eval tst11

def tst12 : MetaM Unit :=
do print "----- tst12 -----";
   withLocalDeclD `x nat $ fun x => do
     let t ← mkEqRefl x >>= mkLambdaFVars #[x];
     print t;
     let type ← inferType t;
     print type;
     isProofQuick t >>= fun b => print (toString b);
     isProofQuick nat >>= fun b => print (toString b);
     isProofQuick type >>= fun b => print (toString b);
     pure ();
   pure ()

/--
info: [Meta.debug] ----- tst12 -----
[Meta.debug] fun x => Eq.refl x
[Meta.debug] ∀ (x : Nat), x = x
[Meta.debug] true
[Meta.debug] false
[Meta.debug] false
-/
#guard_msgs in
#eval tst12

def tst13 : MetaM Unit :=
do print "----- tst13 -----";
   let m₁ ← mkFreshExprMVar (← mkArrow type type);
   let m₂ ← mkFreshExprMVar (mkApp m₁ nat);
   let t  ← mkId m₂;
   print t;
   let r ← abstractMVars t;
   print r.expr;
   let (_, _, e) ← openAbstractMVarsResult r;
   print e;
   pure ()

def mkDecEq (type : Expr) : MetaM Expr := mkAppC `DecidableEq #[type]
def mkStateM (σ : Expr) : MetaM Expr := mkAppC `StateM #[σ]
def mkMonad (m : Expr) : MetaM Expr := mkAppC `Monad #[m]
def mkMonadState (σ m : Expr) : MetaM Expr := mkAppC `MonadState #[σ, m]
def mkAdd (a : Expr) : MetaM Expr := mkAppC `Add #[a]
def mkToString (a : Expr) : MetaM Expr := mkAppC `ToString #[a]

def tst14 : MetaM Unit :=
do print "----- tst14 -----";
   let stateM ← mkStateM nat;
   print stateM;
   let monad ← mkMonad stateM;
   let globalInsts ← getGlobalInstancesIndex;
   let insts ← globalInsts.getUnify monad {};
   print (insts.map (·.val));
   pure ()

/--
info: [Meta.debug] ----- tst14 -----
[Meta.debug] StateM Nat
[Meta.debug] #[@StateT.instMonad]
-/
#guard_msgs in
#eval tst14

def tst15 : MetaM Unit :=
do print "----- tst15 -----";
   let inst ← _root_.mkAdd nat;
   let r ← synthInstance inst;
   print r;
   pure ()

/--
info: [Meta.debug] ----- tst15 -----
[Meta.debug] instAddNat
-/
#guard_msgs in
#eval tst15


def tst16 : MetaM Unit :=
do print "----- tst16 -----";
   let prod ← mkProd nat nat;
   let inst ← mkToString prod;
   print inst;
   let r ← synthInstance inst;
   print r;
   pure ()

/--
info: [Meta.debug] ----- tst16 -----
[Meta.debug] ToString (Nat × Nat)
[Meta.debug] instToStringProd
-/
#guard_msgs in
#eval tst16

def tst17 : MetaM Unit :=
do print "----- tst17 -----";
   let prod ← mkProd nat nat;
   let prod ← mkProd boolE prod;
   let inst ← mkToString prod;
   print inst;
   let r ← synthInstance inst;
   print r;
   pure ()

/--
info: [Meta.debug] ----- tst17 -----
[Meta.debug] ToString (Bool × Nat × Nat)
[Meta.debug] instToStringProd
-/
#guard_msgs in
#eval tst17

def tst18 : MetaM Unit :=
do print "----- tst18 -----";
   let decEqNat ← mkDecEq nat;
   let r ← synthInstance decEqNat;
   print r;
   pure ()

/--
info: [Meta.debug] ----- tst18 -----
[Meta.debug] instDecidableEqNat
-/
#guard_msgs in
#eval tst18

def tst19 : MetaM Unit :=
do print "----- tst19 -----";
   let stateM ← mkStateM nat;
   print stateM;
   let monad ← mkMonad stateM;
   print monad;
   let r ← synthInstance monad;
   print r;
   pure ()

/--
info: [Meta.debug] ----- tst19 -----
[Meta.debug] StateM Nat
[Meta.debug] Monad (StateM Nat)
[Meta.debug] StateT.instMonad
-/
#guard_msgs in
#eval tst19

def tst20 : MetaM Unit :=
do print "----- tst20 -----";
   let stateM ← mkStateM nat;
   print stateM;
   let monadState ← mkMonadState nat stateM;
   print monadState;
   let r ← synthInstance monadState;
   print r;
   pure ()

/--
info: [Meta.debug] ----- tst20 -----
[Meta.debug] StateM Nat
[Meta.debug] MonadState Nat (StateM Nat)
[Meta.debug] instMonadStateOfMonadStateOf Nat (StateM Nat)
-/
#guard_msgs in
#eval tst20

def tst21 : MetaM Unit :=
do print "----- tst21 -----";
   withLocalDeclD `x nat $ fun x => do
   withLocalDeclD `y nat $ fun y => do
   withLocalDeclD `z nat $ fun z => do
   let eq₁ ← mkEq x y;
   let eq₂ ← mkEq y z;
   withLocalDeclD `h₁ eq₁ $ fun h₁ => do
   withLocalDeclD `h₂ eq₂ $ fun h₂ => do
   let h ← mkEqTrans h₁ h₂;
   let h ← mkEqSymm h;
   let h ← mkCongrArg succ h;
   let h₂ ← mkEqRefl succ;
   let h ← mkCongr h₂ h;
   let t ← inferType h;
   check h;
   print h;
   print t;
   let h ← mkCongrFun h₂ x;
   let t ← inferType h;
   check h;
   print t;
   pure ()

/--
info: [Meta.debug] ----- tst21 -----
[Meta.debug] congrArg (fun x => x.succ.succ) (Eq.symm (Eq.trans h₁ h₂))
[Meta.debug] z.succ.succ = x.succ.succ
[Meta.debug] x.succ = x.succ
-/
#guard_msgs in
#eval tst21

def tst22 : MetaM Unit :=
do print "----- tst22 -----";
   withLocalDeclD `x nat $ fun x => do
   withLocalDeclD `y nat $ fun y => do
   let t ← mkAppC `Add.add #[x, y];
   print t;
   let t ← mkAppC `Add.add #[y, x];
   print t;
   let t ← mkAppC `ToString.toString #[x];
   print t;
   pure ()

/--
info: [Meta.debug] ----- tst22 -----
[Meta.debug] Add.add x y
[Meta.debug] Add.add y x
[Meta.debug] toString x
-/
#guard_msgs in
#eval tst22

def test1 : Nat := (fun x y => x + y) 0 1

def tst23 : MetaM Unit :=
do print "----- tst23 -----";
   let cinfo ← getConstInfo `test1;
   let v := cinfo.value?.get!;
   print v;
   print v.headBeta

/--
info: [Meta.debug] ----- tst23 -----
[Meta.debug] (fun x y => x + y) 0 1
[Meta.debug] 0 + 1
-/
#guard_msgs in
#eval tst23

def tst26 : MetaM Unit := do
print "----- tst26 -----";
let m1 ← mkFreshExprMVar (← mkArrow nat nat);
let m2 ← mkFreshExprMVar nat;
let m3 ← mkFreshExprMVar nat;
checkM $ approxDefEq $ isDefEq (mkApp m1 m2) m3;
checkM $ do { let b ← m1.mvarId!.isAssigned; pure (!b) };
checkM $ m3.mvarId!.isAssigned;
pure ()

/-- info: [Meta.debug] ----- tst26 ----- -/
#guard_msgs in
#eval tst26

section
set_option trace.Meta.isDefEq true
set_option trace.Meta.isDefEq.delta true
set_option trace.Meta.isDefEq.assign true

def tst27 : MetaM Unit := do
print "----- tst27 -----";
let m ← mkFreshExprMVar nat;
checkM $ isDefEq (mkNatLit 1) (mkApp (mkConst `Nat.succ) m);
pure ()

#eval tst27
end

def tst28 : MetaM Unit := do
print "----- tst28 -----";
withLocalDeclD `x nat $ fun x =>
withLocalDeclD `y nat $ fun y =>
withLocalDeclD `z nat $ fun z => do
  let t1 ← mkAppM `Add.add #[x, y];
  let t1 ← mkAppM `Add.add #[x, t1];
  let t1 ← mkAppM `Add.add #[t1, t1];
  let t2 ← mkAppM `Add.add #[z, y];
  let t3 ← mkAppM `Eq #[t2, t1];
  let t3 ← mkForallFVars #[z] t3;
  let m  ← mkFreshExprMVar nat;
  let p  ← mkAppM `Add.add #[x, m];
  print t3;
  let r  ← kabstract t3 p;
  print r;
  let p ← mkAppM `Add.add #[x, y];
  let r  ← kabstract t3 p;
  print r;
  pure ()

/--
info: [Meta.debug] ----- tst28 -----
[Meta.debug] ∀ (z : Nat), Add.add z y = Add.add (Add.add x (Add.add x y)) (Add.add x (Add.add x y))
[Meta.debug] ∀ (z : Nat), Add.add z y = Add.add #0 #0
[Meta.debug] ∀ (z : Nat), Add.add z y = Add.add (Add.add x #0) (Add.add x #0)
-/
#guard_msgs in
#eval tst28

def norm : Level → Level := @Lean.Level.normalize

def tst29 : MetaM Unit := do
print "----- tst29 -----";
let u  := mkLevelParam `u;
let v  := mkLevelParam `v;
let u1 := mkLevelSucc u;
let m  := mkLevelMax levelOne u1;
print (norm m);
checkM $ pure $ norm m == u1;
let m  := mkLevelMax u1 levelOne;
print (norm m);
checkM $ pure $ norm m == u1;
let m  := mkLevelMax (mkLevelMax levelOne (mkLevelSucc u1)) (mkLevelSucc levelOne);
checkM $ pure $ norm m == mkLevelSucc u1;
print m;
print (norm m);
let m  := mkLevelMax (mkLevelMax (mkLevelSucc (mkLevelSucc u1)) (mkLevelSucc u1)) (mkLevelSucc levelOne);
print m;
print (norm m);
checkM $ pure $ norm m == mkLevelSucc (mkLevelSucc u1);
let m  := mkLevelMax (mkLevelMax (mkLevelSucc v) (mkLevelSucc u1)) (mkLevelSucc levelOne);
print m;
print (norm m);
pure ()

/--
info: [Meta.debug] ----- tst29 -----
[Meta.debug] u+1
[Meta.debug] u+1
[Meta.debug] max (max 1 (u+2)) 2
[Meta.debug] u+2
[Meta.debug] max (max (u+3) (u+2)) 2
[Meta.debug] u+3
[Meta.debug] max (max (v+1) (u+2)) 2
[Meta.debug] max (u+2) (v+1)
-/
#guard_msgs in
#eval tst29

def tst30 : MetaM Unit := do
print "----- tst30 -----";
let m1 ← mkFreshExprMVar nat;
let m2 ← mkFreshExprMVar (← mkArrow nat nat);
withLocalDeclD `x nat $ fun x => do
  let t := mkApp succ $ mkApp m2 x;
  print t;
  checkM $ approxDefEq $ isDefEq m1 t;
  let r ← instantiateMVars m1;
  print r;
  let r ← instantiateMVars m2;
  print r;
  pure ()

/--
info: [Meta.debug] ----- tst30 -----
[Meta.debug] Nat.succ (?_ x)
[Meta.debug] Nat.succ ?_
[Meta.debug] fun x => ?_
-/
#guard_msgs in
#eval tst30

def tst31 : MetaM Unit := do
print "----- tst31 -----";
let m ← mkFreshExprMVar nat;
let t := mkLet `x nat zero m;
print t;
checkM $ isDefEq t m;
pure ()

def tst32 : MetaM Unit := do
print "----- tst32 -----";
withLocalDeclD `a nat $ fun a => do
withLocalDeclD `b nat $ fun b => do
let aeqb ← mkEq a b;
withLocalDeclD `h2 aeqb $ fun h2 => do
let t ← mkEq (mkApp2 add a a) a;
print t;
let motive := mkLambda `x BinderInfo.default nat (mkApp3 (mkConst `Eq [levelOne]) nat (mkApp2 add a (mkBVar 0)) a);
withLocalDeclD `h1 t $ fun h1 => do
let r ← mkEqNDRec motive h1 h2;
print r;
let rType ← inferType r >>= whnf;
print rType;
check r;
pure ()

/--
info: [Meta.debug] ----- tst32 -----
[Meta.debug] a.add a = a
[Meta.debug] h2 ▸ h1
[Meta.debug] a.add b = a
-/
#guard_msgs in
#eval tst32

def tst33 : MetaM Unit := do
print "----- tst33 -----";
withLocalDeclD `a nat $ fun a => do
withLocalDeclD `b nat $ fun b => do
let aeqb ← mkEq a b;
withLocalDeclD `h2 aeqb $ fun h2 => do
let t ← mkEq (mkApp2 add a a) a;
let motive :=
  mkLambda `x BinderInfo.default nat $
  mkLambda `h BinderInfo.default (mkApp3 (mkConst `Eq [levelOne]) nat a (mkBVar 0)) $
    (mkApp3 (mkConst `Eq [levelOne]) nat (mkApp2 add a (mkBVar 1)) a);
withLocalDeclD `h1 t $ fun h1 => do
let r ← mkEqRec motive h1 h2;
print r;
let rType ← inferType r >>= whnf;
print rType;
check r;
pure ()

/--
info: [Meta.debug] ----- tst33 -----
[Meta.debug] h2 ▸ h1
[Meta.debug] a.add b = a
-/
#guard_msgs in
#eval tst33

def tst34 : MetaM Unit := do
print "----- tst34 -----";
let type := mkSort levelOne;
withLocalDeclD `α type $ fun α => do
  let m ← mkFreshExprMVar type;
  let t ← mkLambdaFVars #[α] (← mkArrow m m);
  print t;
  pure ()

/--
info: [Meta.debug] ----- tst34 -----
[Meta.debug] fun α => ?_ α → ?_ α
-/
#guard_msgs in
#eval tst34

def tst35 : MetaM Unit := do
print "----- tst35 -----";
let type := mkSort levelOne;
withLocalDeclD `α type $ fun α => do
  let m1 ← mkFreshExprMVar type;
  let m2 ← mkFreshExprMVar (← mkArrow nat type);
  let v := mkLambda `x BinderInfo.default nat m1;
  m2.mvarId!.assign v;
  let w := mkApp m2 zero;
  let t1 ← mkLambdaFVars #[α] (← mkArrow w w);
  print t1;
  let m3 ← mkFreshExprMVar type;
  let t2 ← mkLambdaFVars #[α] (← mkArrow (mkBVar 0) (mkBVar 1));
  print t2;
  checkM $ isDefEq t1 t2;
  pure ()

/--
info: [Meta.debug] ----- tst35 -----
[Meta.debug] fun α => ?_ α → ?_ α
[Meta.debug] fun α => α → α
-/
#guard_msgs in
#eval tst35
#check @Id

def tst36 : MetaM Unit := do
print "----- tst36 -----";
let type := mkSort levelOne;
let m1 ← mkFreshExprMVar (← mkArrow type type);
withLocalDeclD `α type $ fun α => do
  let m2 ← mkFreshExprMVar type;
  let t  ← mkAppM `Id #[m2];
  checkM $ approxDefEq $ isDefEq (mkApp m1 α) t;
  checkM $ approxDefEq $ isDefEq m1 (mkConst `Id [levelZero]);
  pure ()

/-- info: [Meta.debug] ----- tst36 ----- -/
#guard_msgs in
#eval tst36

def tst37 : MetaM Unit := do
print "----- tst37 -----";
let m1 ← mkFreshExprMVar (←mkArrow nat (←mkArrow type type));
let m2 ← mkFreshExprMVar (←mkArrow nat type);
withLocalDeclD `v nat $ fun v => do
  let lhs := mkApp2 m1 v (mkApp m2 v);
  let rhs ← mkAppM `StateM #[nat, nat];
  print lhs;
  print rhs;
  checkM $ approxDefEq $ isDefEq lhs rhs;
  pure ()

/--
info: [Meta.debug] ----- tst37 -----
[Meta.debug] ?_ v (?_ v)
[Meta.debug] StateM Nat Nat
-/
#guard_msgs in
#eval tst37

def tst38 : MetaM Unit := do
print "----- tst38 -----";
let m1 ← mkFreshExprMVar nat;
withLocalDeclD `x nat $ fun x => do
let m2 ← mkFreshExprMVar type;
withLocalDeclD `y m2 $ fun y => do
let m3 ← mkFreshExprMVar (←mkArrow m2 nat);
let rhs := mkApp m3 y;
checkM $ approxDefEq $ isDefEq m2 nat;
print m2;
checkM $ getAssignment m2 >>= fun v => pure $ v == nat;
checkM $ approxDefEq $ isDefEq m1 rhs;
print m2;
checkM $ getAssignment m2 >>= fun v => pure $ v == nat;
pure ()

set_option pp.all true
set_option trace.Meta.isDefEq true
set_option trace.Meta.isDefEq.delta true
set_option trace.Meta.isDefEq.assign true

#eval tst38

def tst39 : MetaM Unit := do
print "----- tst39 -----";
withLocalDeclD `α type $ fun α =>
withLocalDeclD `β type $ fun β => do
  let p ← mkProd α β;
  let t ← mkForallFVars #[α, β] p;
  print t;
  let e ← instantiateForall t #[nat, boolE];
  print e;
  pure ()

#eval tst39


def tst40 : MetaM Unit := do
print "----- tst40 -----";
withLocalDeclD `α type $ fun α =>
withLocalDeclD `β type $ fun β =>
withLocalDeclD `a α    $ fun a =>
withLocalDeclD `b β    $ fun b =>
do
  let p ← mkProd α β;
  let t1 ← mkForallFVars #[α, β] p;
  let t2 ← mkForallFVars #[α, β, a, b] p;
  print t1;
  print $ toString $ t1.bindingBody!.hasLooseBVarInExplicitDomain 0 false;
  print $ toString $ t1.bindingBody!.hasLooseBVarInExplicitDomain 0 true;
  print $ toString $ t2.bindingBody!.hasLooseBVarInExplicitDomain 0 false;
  print $ t1.inferImplicit 2 false;
  checkM $ pure $ ((t1.inferImplicit 2 false).bindingInfo! == BinderInfo.default);
  checkM $ pure $ ((t1.inferImplicit 2 false).bindingBody!.bindingInfo! == BinderInfo.default);
  print $ t1.inferImplicit 2 true;
  checkM $ pure $ ((t1.inferImplicit 2 true).bindingInfo! == BinderInfo.implicit);
  checkM $ pure $ ((t1.inferImplicit 2 true).bindingBody!.bindingInfo! == BinderInfo.implicit);
  print t2;
  print $ t2.inferImplicit 2 false;
  checkM $ pure $ ((t2.inferImplicit 2 false).bindingInfo! == BinderInfo.implicit);
  checkM $ pure $ ((t2.inferImplicit 2 false).bindingBody!.bindingInfo! == BinderInfo.implicit);
  print $ t2.inferImplicit 1 false;
  checkM $ pure $ ((t2.inferImplicit 1 false).bindingInfo! == BinderInfo.implicit);
  checkM $ pure $ ((t2.inferImplicit 1 false).bindingBody!.bindingInfo! == BinderInfo.default);
  pure ()

#eval tst40

universe u
structure A (α : Type u) :=
(x y : α)

structure B (α : Type u) :=
(z : α)

structure C (α : Type u) extends A α, B α :=
(w : Bool)

def mkA (x y : Expr) : MetaM Expr := mkAppC `A.mk #[x, y]
def mkB (z : Expr) : MetaM Expr := mkAppC `B.mk #[z]
def mkC (x y z w : Expr) : MetaM Expr := do
let a ← mkA x y;
let b ← mkB z;
mkAppC `C.mk #[a, b, w]

def tst41 : MetaM Unit := do
print "----- tst41 -----";
let c ← mkC (mkNatLit 1) (mkNatLit 2) (mkNatLit 3) boolTrue;
print c;
let x ← mkProjection c `x;
check x;
print x;
let y ← mkProjection c `y;
check y;
print y;
let z ← mkProjection c `z;
check z;
print z;
let w ← mkProjection c `w;
check w;
print w;
pure ()

set_option trace.Meta.isDefEq false
set_option trace.Meta.isDefEq.delta false
set_option trace.Meta.isDefEq.assign false
#eval tst41

set_option pp.all false

def tst42 : MetaM Unit := do
print "----- tst42 -----";
let t ← mkListLit nat [mkRawNatLit 1, mkRawNatLit 2];
print t;
check t;
let t ← mkArrayLit nat [mkRawNatLit 1, mkRawNatLit 2];
print t;
check t;
(match t.arrayLit? with
| some (_, xs) => do
  checkM $ pure $ xs.length == 2;
  (match (xs.get! 0).rawNatLit?, (xs.get! 1).rawNatLit? with
  | some 1, some 2 => pure ()
  | _, _           => throwError "nat lits expected")
| none => throwError "array lit expected")

/--
info: [Meta.debug] ----- tst42 -----
[Meta.debug] [1, 2]
[Meta.debug] #[1, 2]
-/
#guard_msgs in
#eval tst42
