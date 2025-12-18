import Lean.Meta

open Lean
open Lean.Meta

def print (msg : MessageData) : MetaM Unit := do
trace[Meta.debug] msg

def showRecInfo (declName : Name) (majorPos? : Option Nat := none) : MetaM Unit := do
let info ← mkRecursorInfo declName majorPos?
print (toString info)

set_option trace.Meta true
set_option trace.Meta.isDefEq false

#eval showRecInfo `Acc.recOn
#eval showRecInfo `Prod.casesOn
#eval showRecInfo `List.recOn
#eval showRecInfo `List.casesOn
#eval showRecInfo `List.brecOn

#eval showRecInfo `Iff.elim (some 4)
