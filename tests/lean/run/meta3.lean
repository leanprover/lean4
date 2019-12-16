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
do v? ← getExprMVarAssignment? m.mvarId!;
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
def add  := mkAppN (mkConst `HasAdd.add [levelZero]) #[nat, mkConst `Nat.HasAdd]

def tst1 : MetaM Unit :=
do let d : DiscrTree Nat := {};
   mvar ← mkFreshExprMVar nat;
   d ← d.insert (mkAppN add #[mvar, mkNatLit 10]) 1;
   d ← d.insert (mkAppN add #[mkNatLit 0, mkNatLit 10]) 2;
   d ← d.insert (mkAppN (mkConst `Nat.add) #[mkNatLit 0, mkNatLit 20]) 3;
   d ← d.insert (mkAppN add #[mvar, mkNatLit 20]) 4;
   d ← d.insert mvar 5;
   print (format d);
   vs ← d.getMatch (mkAppN add #[mkNatLit 1, mkNatLit 10]);
   print (format vs);
   let t := mkAppN add #[mvar, mvar];
   print t;
   vs ← d.getMatch t;
   print (format vs);
   vs ← d.getUnify t;
   print (format vs);
   vs ← d.getUnify mvar;
   print (format vs);
   vs ← d.getUnify $ mkAppN add #[mkNatLit 0, mvar];
   print (format vs);
   vs ← d.getUnify $ mkAppN add #[mvar, mkNatLit 20];
   print (format vs);
   pure ()

#eval run [`Init.Data.Nat] tst1
