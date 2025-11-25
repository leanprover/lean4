/-
Copyright (c) 2022 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Lean.Meta.Eval
public import Lean.Elab.SyntheticMVars

public section

namespace Lean.Elab.Term
open Meta

unsafe def evalTerm (α) (type : Expr) (value : Syntax) (safety := DefinitionSafety.safe) : TermElabM α := withoutModifyingEnv do
  let v ← elabTermEnsuringType value type
  synthesizeSyntheticMVarsNoPostponing
  let v ← instantiateMVars v
  if (← logUnassignedUsingErrorInfos (← getMVars v)) then throwAbortTerm
  evalExpr α type v safety

end Lean.Elab.Term
