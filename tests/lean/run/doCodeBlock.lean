import Lean

new_frontend

namespace Lean.Elab.Term.Do

def ref := Syntax.missing

def vdecl (name : Name) (pure := true) : VarDecl :=
{ ref := ref, name := name, pure := pure, letDecl := Syntax.missing }

def print (c : CodeBlock) : TermElabM Unit := do
let msg := c.toMessageData
let msg ← addMessageContext msg
IO.println (← liftIO msg.toString)
pure ()

def tst : TermElabM Unit := do
let x := mkIdentFrom ref `x
let c ← mkIte ref (← `($x < 1))
  (mkVarDecl (vdecl `w) (mkVarDecl (vdecl `z) (← mkReassign (vdecl `x) (mkReturn ref))))
  (mkVarDecl (vdecl `x) (← mkReassign (vdecl `y) (mkBreak ref)))
print c
IO.println "-----"
let c ← concat c (mkVarDecl (vdecl `w) (← mkReassign (vdecl `z) (mkReturn ref)))
print c
let c ← mkReassign (vdecl `w) c
IO.println "-----"
print c
pure ()

#eval tst


end Lean.Elab.Term.Do
