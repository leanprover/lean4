import Init.Lean.Meta
open Lean
open Lean.Meta

def dbgOpt : Options :=
let opt : Options := {};
let opt := opt.setBool `trace.Meta true;
let opt := opt.setBool `trace.Meta.isDefEq.step false;
let opt := opt.setBool `trace.Meta.isDefEq.delta false;
let opt := opt.setBool `trace.Meta.isDefEq.assign false;
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

def nat   := mkConst `Nat
def boolE := mkConst `Bool
def succ  := mkConst `Nat.succ
def add   := mkConst `Nat.add
def io    := mkConst `IO
def type  := mkSort levelOne

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

def mkDecEq (type : Expr) : MetaM Expr :=
do u ← getLevel type;
   pure $ mkApp (mkConst `DecidableEq [u]) type

def mkStateM (σ : Expr) : MetaM Expr :=
do u ← getLevel σ;
   (some u) ← pure u.dec | throw $ Exception.other "failed to create StateM application";
   let r := mkApp (mkConst `StateM [u]) σ;
   check r;
   pure r

def mkMonad (m : Expr) : MetaM Expr :=
do u ← mkFreshLevelMVar;
   v ← mkFreshLevelMVar;
   let arrow := mkArrow (mkSort (mkLevelSucc u)) (mkSort (mkLevelSucc v));
   mType ← inferType m;
   mType ← whnf mType;
   print arrow;
   print mType;
   condM (isDefEq arrow mType)
     (do u ← instantiateLevelMVars u;
         v ← instantiateLevelMVars v;
         let r := mkApp (mkConst `Monad [u, v]) m;
         print r;
         check r;
         pure r)
     (throw $ Exception.other "failed to create Monad application")

def mkMonadState (σ m : Expr) : MetaM Expr :=
do u ← getLevel σ;
   (some u) ← pure u.dec | throw $ Exception.other "failed to create MonadState application";
   mType ← inferType m;
   v ← mkFreshLevelMVar;
   w ← mkFreshLevelMVar;
   let arrow := mkArrow (mkSort (mkLevelSucc v)) (mkSort (mkLevelSucc w));
   mType ← whnf mType;
   print arrow;
   print mType;
   condM (isDefEq arrow mType)
     (do w ← instantiateLevelMVars w;
         let r := mkAppB (mkConst `MonadState [u, w]) σ m;
         print r;
         check r;
         pure r)
     (throw $ Exception.other "failed to create MonadState application")

def mkHasAdd (a : Expr) : MetaM Expr :=
do u ← getLevel a;
   (some u) ← pure u.dec | throw $ Exception.other "failed to create HasAdd application";
   let r := mkApp (mkConst `HasAdd [u]) a;
   print r;
   check r;
   pure r

def mkHasToString (a : Expr) : MetaM Expr :=
do u ← getLevel a;
   (some u) ← pure u.dec | throw $ Exception.other "failed to create HasToString application";
   let r := mkApp (mkConst `HasToString [u]) a;
   print r;
   check r;
   pure r

def tst14 : MetaM Unit :=
do print "----- tst14 -----";
   stateM ← mkStateM nat;
   print stateM;
   monad ← mkMonad stateM;
   globalInsts ← getGlobalInstances;
   insts ← globalInsts.getUnify monad;
   print insts;
   pure ()

#eval run [`Init.Control.State] tst14

def tst15 : MetaM Unit :=
do print "----- tst15 -----";
   inst ← mkHasAdd nat;
   (some r) ← synthInstance inst | throw $ Exception.other "failed `HasAdd Nat`";
   print r;
   pure ()

#eval run [`Init.Control.State] tst15

def tst16 : MetaM Unit :=
do print "----- tst16 -----";
   prod ← mkProd nat nat;
   inst ← mkHasToString prod;
   print inst;
   (some r) ← synthInstance inst | throw $ Exception.other "failed `HasToString (Nat × Nat)`";
   print r;
   pure ()

#eval run [`Init.Control.State] tst16

def tst17 : MetaM Unit :=
do print "----- tst17 -----";
   prod ← mkProd nat nat;
   prod ← mkProd boolE prod;
   inst ← mkHasToString prod;
   print inst;
   (some r) ← synthInstance inst | throw $ Exception.other "failed `HasToString (Bool × (Nat × Nat))`";
   print r;
   pure ()

#eval run [`Init.Control.State] tst17

def tst18 : MetaM Unit :=
do print "----- tst18 -----";
   decEqNat ← mkDecEq nat;
   (some r) ← synthInstance decEqNat | throw $ Exception.other "failed `DecidableEq Nat`";
   print r;
   pure ()

#eval run [`Init.Control.State] tst18

def tst19 : MetaM Unit :=
do print "----- tst19 -----";
   stateM ← mkStateM nat;
   print stateM;
   monad ← mkMonad stateM;
   print monad;
   (some r) ← synthInstance monad | throw $ Exception.other "failed `Monad (StateM Nat)`";
   print r;
   pure ()

#eval run [`Init.Control.State] tst19

def tst20 : MetaM Unit :=
do print "----- tst20 -----";
   stateM ← mkStateM nat;
   print stateM;
   monadState ← mkMonadState nat stateM;
   print monadState;
   (some r) ← synthInstance monadState | throw $ Exception.other "failed `MonadState Nat (StateM Nat)`";
   print r;
   pure ()

#eval run [`Init.Control.State] tst20

def tst21 : MetaM Unit :=
do print "----- tst21 -----";
   withLocalDeclD `x nat $ fun x => do
   withLocalDeclD `y nat $ fun y => do
   withLocalDeclD `z nat $ fun z => do
   eq₁ ← mkEq x y;
   eq₂ ← mkEq y z;
   withLocalDeclD `h₁ eq₁ $ fun h₁ => do
   withLocalDeclD `h₂ eq₂ $ fun h₂ => do
   h ← mkEqTrans h₁ h₂;
   h ← mkEqSymm h;
   h ← mkCongrArg succ h;
   h₂ ← mkEqRefl succ;
   h ← mkCongr h₂ h;
   t ← inferType h;
   check h;
   print h;
   print t;
   h ← mkCongrFun h₂ x;
   t ← inferType h;
   check h;
   print t;
   pure ()

#eval run [`Init.Core] tst21
