import Lean

new_frontend

namespace Lean.Elab.Term.Do

def ref := Syntax.missing

def mkVarDecl (x : Name) (k : CodeBlock) : CodeBlock :=
mkVarDeclCore #[x] Syntax.missing k

def mkReassign (x : Name) (k : CodeBlock) : TermElabM CodeBlock :=
mkReassignCore #[x] Syntax.missing k

def print (c : CodeBlock) : TermElabM Unit := do
let msg := c.toMessageData
let msg ← addMessageContext msg
IO.println (← liftIO msg.toString)
pure ()

def tst : TermElabM Unit := do
let x := mkIdentFrom ref `x
let c ← mkIte ref mkNullNode (← `($x < 1))
  (mkVarDecl `w (mkVarDecl `z (← mkReassign `x (mkReturn ref))))
  (mkVarDecl `x (← mkReassign `y (mkBreak ref)))
print c
IO.println "-----"
let c ← concat c (mkVarDecl `w (← mkReassign `z (mkReturn ref)))
print c
let c ← mkReassign `w c
IO.println "-----"
print c
pure ()

#eval tst


end Lean.Elab.Term.Do
