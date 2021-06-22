import Lean.Meta

open Lean
open Lean.Meta

def print (msg : MessageData) : MetaM Unit := do
trace[Meta.debug] msg

def checkM (x : MetaM Bool) : MetaM Unit :=
unless (← x) do throwError "check failed"

axiom Ax : forall (α β : Type), α → β → DecidableEq β

set_option trace.Meta.debug true

def tst1 : MetaM Unit := do
let cinfo ← getConstInfo `Ax;
let (_, _, e) ← forallMetaTelescopeReducing cinfo.type (some 0);
checkM (pure (!e.hasMVar));
print e;
let (_, _, e) ← forallMetaTelescopeReducing cinfo.type (some 1);
checkM (pure e.hasMVar);
checkM (pure e.isForall);
print e;
let (_, _, e) ← forallMetaTelescopeReducing cinfo.type (some 5);
checkM (pure e.hasMVar);
checkM (pure e.isForall);
print e;
let (_, _, e) ← forallMetaTelescopeReducing cinfo.type (some 6);
checkM (pure e.hasMVar);
checkM (pure (!e.isForall));
print e;
let (_, _, e') ← forallMetaTelescopeReducing cinfo.type;
print e';
checkM (isDefEq e e');
forallBoundedTelescope cinfo.type (some 0) $ fun xs body => checkM (pure (xs.size == 0));
forallBoundedTelescope cinfo.type (some 1) $ fun xs body => checkM (pure (xs.size == 1));
forallBoundedTelescope cinfo.type (some 6) $ fun xs body => do { print xs; checkM (pure (xs.size == 6)) };
forallBoundedTelescope cinfo.type (some 10) $ fun xs body => do { print xs; checkM (pure (xs.size == 6)) };
pure ()

#eval tst1
