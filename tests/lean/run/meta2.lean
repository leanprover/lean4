import Init.Lean.Meta
open Lean
open Lean.Meta

def dbgOpt : Options :=
let opt : Options := {};
let opt := opt.setBool `trace.Meta true;
-- let opt := opt.setBool `trace.Meta.check false;
opt

def print (msg : MessageData) : MetaM Unit :=
trace! `Meta.debug msg

def check (x : MetaM Bool) : MetaM Unit :=
unlessM x $ throw $ Exception.other "check failed"

def getAssignment (m : Expr) : MetaM Expr :=
do v? ← getExprMVarAssignment m.mvarId!;
   match v? with
   | some v => pure v
   | none   => throw $ Exception.other "metavariable is not assigned"

def run (mods : List Name) (x : MetaM Unit) (opts : Options := dbgOpt) : IO Unit :=
do env ← importModules $ mods.map $ fun m => {module := m};
   match x { config := { opts := opts } } { env := env } with
   | EStateM.Result.ok _ s    => do
     s.traceState.traces.forM $ fun m => IO.println $ format m;
     pure ()
   | EStateM.Result.error err s => do
     s.traceState.traces.forM $ fun m => IO.println $ format m;
     throw (IO.userError (toString err))

def nat  := mkConst `Nat
def succ := mkConst `Nat.succ
def add  := mkConst `Nat.add
def io   := mkConst `IO
def type := mkSort levelOne

def tst1 : MetaM Unit :=
do print "----- tst1 -----";
   mvar ← mkFreshExprMVar nat;
   check $ isExprDefEq mvar (mkNatLit 10);
   check $ isExprDefEq mvar (mkNatLit 10);
   pure ()

#eval run [`Init.Data.Nat] tst1

def tst2 : MetaM Unit :=
do print "----- tst2 -----";
   mvar ← mkFreshExprMVar nat;
   check $ isExprDefEq (mkApp succ mvar) (mkApp succ (mkNatLit 10));
   check $ isExprDefEq mvar (mkNatLit 10);
   pure ()

#eval run [`Init.Data.Nat] tst2

def tst3 : MetaM Unit :=
do print "----- tst3 -----";
   let t   := mkLambda `x BinderInfo.default nat $ mkBVar 0;
   mvar ← mkFreshExprMVar (mkForall `x BinderInfo.default nat nat);
   lambdaTelescope t $ fun xs _ => do {
     let x := xs.get! 0;
     check $ isExprDefEq (mkApp mvar x) (mkAppN add #[x, mkAppN add #[mkNatLit 10, x]]);
     pure ()
   };
   v ← getAssignment mvar;
   print v;
   pure ()

#eval run [`Init.Data.Nat] tst3

def tst4 : MetaM Unit :=
do print "----- tst4 -----";
   let t   := mkLambda `x BinderInfo.default nat $ mkBVar 0;
   lambdaTelescope t $ fun xs _ => do {
     let x := xs.get! 0;
     mvar ← mkFreshExprMVar (mkForall `x BinderInfo.default nat nat);
     -- the following `isExprDefEq` fails because `x` is also in the context of `mvar`
     check $ not <$> isExprDefEq (mkApp mvar x) (mkAppN add #[x, mkAppN add #[mkNatLit 10, x]]);
     check $ approxDefEq $ isExprDefEq (mkApp mvar x) (mkAppN add #[x, mkAppN add #[mkNatLit 10, x]]);
     v ← getAssignment mvar;
     print v;
     pure ()
   };
   pure ()

#eval run [`Init.Data.Nat] tst4

def mkProd (a b : Expr) : MetaM Expr :=
do u ← getLevel a;
   v ← getLevel b;
   let r := mkAppN (mkConst `Prod [u.dec.getD u, v.dec.getD v]) #[a, b];
   check r;
   pure r

def mkPair (a b : Expr) : MetaM Expr :=
do aType ← inferType a;
   bType ← inferType b;
   u ← getLevel aType;
   v ← getLevel bType;
   let r := mkAppN (mkConst `Prod.mk [u.dec.getD u, v.dec.getD v]) #[aType, bType, a, b];
   check r;
   pure r

def mkEq (a b : Expr) : MetaM Expr :=
do aType ← inferType a;
   u ← getLevel aType;
   let r := mkAppN (mkConst `Eq [u]) #[aType, a, b];
   check r;
   pure r

def mkEqRefl (a : Expr) : MetaM Expr :=
do aType ← inferType a;
   u ← getLevel aType;
   let r := mkAppN (mkConst `Eq.refl [u]) #[aType, a];
   check r;
   pure r

def mkFst (s : Expr) : MetaM Expr :=
do sType ← inferType s;
   sType ← whnfUsingDefault sType;
   unless (sType.isAppOfArity `Prod 2) $ throw $ Exception.other "product expected";
   let lvls := sType.getAppFn.constLevels!;
   let r := mkAppN (mkConst `Prod.fst lvls) #[sType.getArg! 0, sType.getArg! 1, s];
   check r;
   pure r

def mkSnd (s : Expr) : MetaM Expr :=
do sType ← inferType s;
   sType ← whnfUsingDefault sType;
   unless (sType.isAppOfArity `Prod 2) $ throw $ Exception.other "product expected";
   let lvls := sType.getAppFn.constLevels!;
   let r := mkAppN (mkConst `Prod.snd lvls) #[sType.getArg! 0, sType.getArg! 1, s];
   check r;
   pure r

def mkId (a : Expr) : MetaM Expr :=
do aType ← inferType a;
   lvl   ← getLevel aType;
   let r := mkAppN (mkConst `id [lvl]) #[aType, a];
   check r;
   pure r

#print id

def tst5 : MetaM Unit :=
do print "----- tst5 -----";
   p₁ ← mkPair (mkNatLit 1) (mkNatLit 2);
   x  ← mkFst p₁;
   print x;
   v  ← whnf x;
   print v;
   v  ← usingTransparency TransparencyMode.reducible $ whnf x;
   print v;
   x  ← mkId x;
   print x;
   prod ← mkProd nat nat;
   m ← mkFreshExprMVar prod;
   y ← mkFst m;
   check $ isExprDefEq y x;
   print y

#eval run [`Init.Data.Nat] tst5

def tst6 : MetaM Unit :=
do print "----- tst6 -----";
   withLocalDecl `x nat BinderInfo.default $ fun x => do
     m ← mkFreshExprMVar nat;
     let t := mkAppN add #[m, mkNatLit 4];
     let s := mkAppN add #[x, mkNatLit 3];
     check $ not <$> isExprDefEq t s;
     let s := mkAppN add #[x, mkNatLit 6];
     check $ isExprDefEq t s;
     v ← getAssignment m;
     check $ pure $ v == mkAppN add #[x, mkNatLit 2];
     print v;
     m ← mkFreshExprMVar nat;
     let t := mkAppN add #[m, mkNatLit 4];
     let s := mkNatLit 3;
     check $ not <$> isExprDefEq t s;
     let s := mkNatLit 10;
     check $ isExprDefEq t s;
     v ← getAssignment m;
     check $ pure $ v == mkNatLit 6;
     print v;
     pure ()

#eval run [`Init.Data.Nat] tst6

def mkArrow (d b : Expr) : Expr := mkForall `_ BinderInfo.default d b

def tst7 : MetaM Unit :=
do print "----- tst7 -----";
   withLocalDecl `x type BinderInfo.default $ fun x => do
     m1 ← mkFreshExprMVar (mkArrow type type);
     m2 ← mkFreshExprMVar type;
     let t := mkApp io x;
     -- we need to use foApprox to solve `?m1 ?m2 =?= IO x`
     check $ not <$> isDefEq (mkApp m1 m2) t;
     check $ approxDefEq $ isDefEq (mkApp m1 m2) t;
     v ← getAssignment m1;
     check $ pure $ v == io;
     v ← getAssignment m2;
     check $ pure $ v == x;
     pure ()

#eval run [`Init.System.IO] tst7

def tst8 : MetaM Unit :=
do print "----- tst8 -----";
   let add := mkAppN (mkConst `HasAdd.add [levelOne]) #[nat, mkConst `Nat.HasAdd];
   let t   := mkAppN add #[mkNatLit 2, mkNatLit 3];
   t ← usingTransparency TransparencyMode.reducible $ whnf t;
   print t;
   t ← whnf t;
   print t;
   t ← reduce t;
   print t;
   pure ()

#eval run [`Init.Core] tst8

def tst9 : MetaM Unit :=
do print "----- tst9 -----";
   env ← getEnv;
   print (toString $ Lean.isReducible env `Prod.fst);
   print (toString $ Lean.isReducible env `HasAdd.add);
   pure ()

#eval run [`Init.Core] tst9

def tst10 : MetaM Unit :=
do print "----- tst10 -----";
   t ← withLocalDecl `x nat BinderInfo.default $ fun x => do {
     let b := mkAppN add #[x, mkAppN add #[mkNatLit 2, mkNatLit 3]];
     mkLambda #[x] b
   };
   print t;
   t ← reduce t;
   print t;
   pure ()

#eval run [`Init.Core] tst10

def tst11 : MetaM Unit :=
do print "----- tst11 -----";
   check $ isType nat;
   check $ isType (mkArrow nat nat);
   check $ not <$> isType add;
   check $ not <$> isType (mkNatLit 1);
   withLocalDecl `x nat BinderInfo.default $ fun x => do {
     check $ not <$> isType x;
     check $ not <$> (mkLambda #[x] x >>= isType);
     check $ not <$> (mkLambda #[x] nat >>= isType);
     t ← mkEq x (mkNatLit 0) >>= mkForall #[x];
     print t;
     check $ isType t;
     pure ()
   };
   pure ()

#eval run [`Init.Core] tst11

def tst12 : MetaM Unit :=
do print "----- tst12 -----";
   withLocalDecl `x nat BinderInfo.default $ fun x => do {
     t ← mkEqRefl x >>= mkLambda #[x];
     print t;
     type ← inferType t;
     print type;
     isProofQuick t >>= fun b => print (toString b);
     isProofQuick nat >>= fun b => print (toString b);
     isProofQuick type >>= fun b => print (toString b);
     pure ()
   };
   pure ()

#eval run [`Init.Core] tst12

def tst13 : MetaM Unit :=
do print "----- tst13 -----";
   m₁ ← mkFreshExprMVar (mkArrow type type);
   m₂ ← mkFreshExprMVar (mkApp m₁ nat);
   t  ← mkId m₂;
   print t;
   r ← abstractMVars t;
   print r.expr;
   (_, _, e) ← openAbstractMVarsResult r;
   print e;
   pure ()

#eval run [`Init.Core] tst13
