/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Lean.Elab.Term
import Init.Lean.Elab.Tactic.Basic

namespace Lean
namespace Elab

namespace Term

def mkTacticMVar (ref : Syntax) (type : Expr) (tacticCode : Syntax) : TermElabM Expr := do
mvar ← mkFreshExprMVar ref type MetavarKind.synthetic;
let mvarId := mvar.mvarId!;
registerSyntheticMVar ref mvarId $ SyntheticMVarKind.tactic tacticCode;
pure mvar

@[builtinTermElab tacticBlock] def elabTacticBlock : TermElab :=
fun stx expectedType? =>
  match expectedType? with
  | some expectedType => mkTacticMVar stx expectedType (stx.getArg 1)
  | none => throwError stx ("invalid tactic block, expected type has not been provided")


end Term

end Elab
end Lean
