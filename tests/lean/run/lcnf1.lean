import Lean

open Lean Compiler Meta

def test (declName : Name) : MetaM Unit := do
  let .defnInfo info ← getConstInfo declName | throwError "definition expected"
  let val ← ToLCNF.toLCNF {} (← macroInline info.value)
  IO.println (← ppExpr val)

#eval test ``Lean.Elab.Term.synthesizeInstMVarCore
