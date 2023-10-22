import Lean.Meta

open Lean
open Lean.Meta

def dbgOpt : Options :=
let opt : Options := {};
let opt := opt.setBool `trace.Meta true;
-- let opt := opt.setBool `trace.Meta.check false;
opt

def print (msg : MessageData) : MetaM Unit := do
trace[Meta.debug] msg

def check (x : MetaM Bool) : MetaM Unit :=
unless (← x) do throwError "check failed"

def getAssignment (m : Expr) : MetaM Expr :=
do let v? ← getExprMVarAssignment? m.mvarId!;
   (match v? with
   | some v => pure v
   | none   => throwError "metavariable is not assigned")

unsafe def run (mods : Array Name) (x : MetaM Unit) (opts : Options := dbgOpt) : IO Unit :=
 withImportModules (mods.map $ fun m => {module := m}) {} 0 fun env => do
   let x : MetaM Unit := do { x; printTraces };
   discard $ x.toIO { options := opts, fileName := "", fileMap := default } { env := env };
   pure ()

def nat  := mkConst `Nat
def succ := mkConst `Nat.succ
def add  := mkAppN (mkConst `Add.add [levelZero]) #[nat, mkConst `Nat.add]

def tst1 : MetaM Unit :=
do let d : DiscrTree Nat := {};
   let mvar ← mkFreshExprMVar nat;
   let d ← d.insert (mkAppN add #[mvar, mkNatLit 10]) 1 {};
   let d ← d.insert (mkAppN add #[mkNatLit 0, mkNatLit 10]) 2 {};
   let d ← d.insert (mkAppN (mkConst `Nat.add) #[mkNatLit 0, mkNatLit 20]) 3 {};
   let d ← d.insert (mkAppN add #[mvar, mkNatLit 20]) 4 {};
   let d ← d.insert mvar 5 {};
   print (format d);
   let vs ← d.getMatch (mkAppN add #[mkNatLit 1, mkNatLit 10]) {};
   print (format vs);
   let t := mkAppN add #[mvar, mvar];
   print t;
   let vs ← d.getMatch t {};
   print (format vs);
   let vs ← d.getUnify t {};
   print (format vs);
   let vs ← d.getUnify mvar {};
   print (format vs);
   let vs ← d.getUnify (mkAppN add #[mkNatLit 0, mvar]) {};
   print (format vs);
   let vs ← d.getUnify (mkAppN add #[mvar, mkNatLit 20]) {};
   print (format vs);
   pure ()

#eval run #[`Init.Data.Nat] tst1
