import Init.Lean.Meta
open Lean
open Lean.Meta

def print (msg : MessageData) : MetaM Unit :=
trace! `Meta.debug msg

def check (x : MetaM Bool) : MetaM Unit :=
unlessM x $ throw $ Exception.other "check failed"

axiom Ax : forall (α β : Type), α → β → DecidableEq β

set_option trace.Meta true

def tst1 : MetaM Unit := do
cinfo ← getConstInfo `Ax;
(_, _, e) ← forallMetaTelescopeReducing cinfo.type (some 0);
check (pure (!e.hasMVar));
print e;
(_, _, e) ← forallMetaTelescopeReducing cinfo.type (some 1);
check (pure e.hasMVar);
check (pure e.isForall);
print e;
(_, _, e) ← forallMetaTelescopeReducing cinfo.type (some 5);
check (pure e.hasMVar);
check (pure e.isForall);
print e;
(_, _, e) ← forallMetaTelescopeReducing cinfo.type (some 6);
check (pure e.hasMVar);
check (pure (!e.isForall));
print e;
(_, _, e') ← forallMetaTelescopeReducing cinfo.type;
print e';
check (isDefEq e e');
pure ()

#eval tst1
