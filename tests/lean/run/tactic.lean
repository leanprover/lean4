import Init.Lean.Meta
open Lean
open Lean.Meta

axiom simple : forall {p q : Prop}, p → q → p

def print (msg : MessageData) : MetaM Unit :=
trace! `Meta.Tactic msg

set_option trace.Meta.Tactic true

def tst1 : MetaM Unit :=
do cinfo ← getConstInfo `simple;
   mvar  ← mkFreshExprSyntheticOpaqueMVar cinfo.type;
   let mvarId := mvar.mvarId!;
   (_, mvarId) ← introN mvarId 4;
   assumption mvarId;
   result ← instantiateMVars mvar;
   print result

#eval tst1
