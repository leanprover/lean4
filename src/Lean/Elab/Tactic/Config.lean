/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Tactic.Basic
import Lean.Elab.SyntheticMVars

namespace Lean.Elab.Tactic
open Meta
macro "declare_config_elab" elabName:ident type:ident : command =>
 `(unsafe def evalUnsafe (e : Expr) : TermElabM $type :=
    Term.evalExpr $type ``$type e
   @[implementedBy evalUnsafe] constant eval (e : Expr) : TermElabM $type
   def $elabName (optConfig : Syntax) : TermElabM $type := do
     if optConfig.isNone then
       return { : $type }
     else
       withoutModifyingState <| withLCtx {} {} <| Term.withSynthesize do
         let c ← Term.elabTermEnsuringType optConfig[0][3] (Lean.mkConst ``$type)
         eval (← instantiateMVars c)
  )

end Lean.Elab.Tactic
