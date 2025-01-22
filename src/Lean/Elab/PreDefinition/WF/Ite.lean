/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Transform
import Lean.Elab.Tactic.Simp

namespace Lean.Meta

private def getContext : MetaM Simp.Context := do
  let s : SimpTheorems := {}
  let s ← s.addConst ``dite_eq_ite (inv := true)
  Simp.mkContext
    (simpTheorems  := #[s])
    (congrTheorems := {})
    (config        := { Simp.neutralConfig with dsimp := false })

def iteToDIte (e : Expr) : MetaM Expr := do
  let ctx ← getContext
  let (result, _) ← Meta.simp e ctx
  let e' := result.expr
  trace[Elab.definition.wf] "Attach-introduction:{indentExpr e}\nto{indentExpr e'}"
  return e'

/-
run_elab do
  let stx ← `(fun (n : Nat) => if n > 0 then 3 else 4)
  let e ← Elab.Term.elabTerm stx .none
  let e' ← iteToDIte e
  logInfo m!"{e}\n{e'}"
-/


end Lean.Meta
