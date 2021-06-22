import Lean.Meta


open Lean
open Lean.Meta

axiom simple : forall {p q : Prop}, p → q → p

def print (msg : MessageData) : MetaM Unit := do
trace[Meta.Tactic] msg

def tst1 : MetaM Unit := do
let cinfo ← getConstInfo `simple
let mvar  ← mkFreshExprSyntheticOpaqueMVar cinfo.type
let mvarId := mvar.mvarId!
let (_, mvarId) ← introN mvarId 4
assumption mvarId
let result ← instantiateMVars mvar
print result

set_option trace.Meta.Tactic true

#eval tst1
