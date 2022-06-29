/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Eval
import Lean.Elab.Tactic.Basic
import Lean.Elab.SyntheticMVars

namespace Lean.Elab.Tactic
open Meta
macro "declare_config_elab" elabName:ident type:ident : command =>
 `(unsafe def evalUnsafe (e : Expr) : TermElabM $type :=
    Meta.evalExpr' (safety := .unsafe) $type ``$type e
   @[implementedBy evalUnsafe] opaque eval (e : Expr) : TermElabM $type
   def $elabName (optConfig : Syntax) : TermElabM $type := do
     if optConfig.isNone then
       return { : $type }
     else
       let c ← withoutModifyingState <| withLCtx {} {} <| withSaveInfoContext <| Term.withSynthesize do
         let c ← Term.elabTermEnsuringType optConfig[0][3] (Lean.mkConst ``$type)
         Term.synthesizeSyntheticMVarsNoPostponing
         instantiateMVars c
       eval c
  )

end Lean.Elab.Tactic
