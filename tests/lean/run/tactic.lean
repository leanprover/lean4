import Lean.Meta
new_frontend

open Lean
open Lean.Meta

axiom simple : forall {p q : Prop}, p → q → p

def print (msg : MessageData) : MetaM Unit :=
trace! `Meta.Tactic msg

def tst1 : MetaM Unit :=
do cinfo ← getConstInfo `simple;
   mvar  ← mkFreshExprSyntheticOpaqueMVar cinfo.type;
   let mvarId := mvar.mvarId!;
   (_, mvarId) ← introN mvarId 4;
   assumption mvarId;
   result ← instantiateMVars mvar;
   print result

set_option trace.Meta.Tactic true

#eval tst1
