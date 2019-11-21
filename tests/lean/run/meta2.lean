import Init.Lean.Meta
open Lean
open Lean.Meta

def dbgOpt : Options :=
let opt : Options := {};
let opt := opt.setBool `trace.Meta.debug true;
let opt := opt.setBool `trace.Meta.isDefEq true;
opt

def print (msg : MessageData) : MetaM Unit :=
trace! `Meta.debug msg

def run (mods : List Name) (x : MetaM Unit) (opts : Options := dbgOpt) : IO Unit :=
do env ← importModules $ mods.map $ fun m => {module := m};
   match x { config := { opts := opts } } { env := env } with
   | EStateM.Result.ok _ s    => do
     s.traceState.traces.forM $ fun m => IO.println $ format m;
     pure ()
   | EStateM.Result.error err _ => throw (IO.userError (toString err))

def tst1 : MetaM Unit :=
do print "----- tst1 -----";
   let nat := mkConst `Nat;
   mvar ← mkFreshExprMVar nat;
   isExprDefEq mvar (mkNatLit 10);
   isExprDefEq mvar (mkNatLit 10);
   pure ()

#eval run [`Init.Data.Nat] tst1

def tst2 : MetaM Unit :=
do print "----- tst2 -----";
   let nat  := mkConst `Nat;
   let succ := mkConst `Nat.succ;
   mvar ← mkFreshExprMVar nat;
   isExprDefEq (mkApp succ mvar) (mkApp succ (mkNatLit 10));
   isExprDefEq mvar (mkNatLit 10);
   pure ()

#eval run [`Init.Data.Nat] tst2

def tst3 : MetaM Unit :=
do print "----- tst3 -----";
   let nat := mkConst `Nat;
   let add := mkConst `Nat.add;
   let t   := mkLambda `x BinderInfo.default nat $ mkBVar 0;
   mvar ← mkFreshExprMVar (mkForall `x BinderInfo.default nat nat);
   lambdaTelescope t $ fun xs _ => do {
     let x := xs.get! 0;
     isExprDefEq (mkApp mvar x) (mkAppN add #[x, mkAppN add #[mkNatLit 10, x]]);
     pure ()
   };
   some v ← getExprMVarAssignment mvar.mvarId! | pure ();
   print v;
   pure ()

#eval run [`Init.Data.Nat] tst3
