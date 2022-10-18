/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Eval
import Lean.Elab.Tactic.Basic
import Lean.Elab.SyntheticMVars
import Lean.Linter.MissingDocs

namespace Lean.Elab.Tactic
open Meta
macro (name := configElab) doc?:(docComment)? "declare_config_elab" elabName:ident type:ident : command =>
 `(unsafe def evalUnsafe (e : Expr) : TermElabM $type :=
    Meta.evalExpr' (safety := .unsafe) $type ``$type e
   @[implemented_by evalUnsafe] opaque eval (e : Expr) : TermElabM $type
   $[$doc?:docComment]?
   def $elabName (optConfig : Syntax) : TermElabM $type := do
     if optConfig.isNone then
       return { : $type }
     else
       let c ← withoutModifyingStateWithInfoAndMessages <| withLCtx {} {} <| withSaveInfoContext <| Term.withSynthesize do
         let c ← Term.elabTermEnsuringType optConfig[0][3] (Lean.mkConst ``$type)
         Term.synthesizeSyntheticMVarsNoPostponing
         instantiateMVars c
       eval c
  )

open Linter.MissingDocs in
@[builtin_missing_docs_handler Elab.Tactic.configElab]
def checkConfigElab : SimpleHandler := mkSimpleHandler "config elab"

end Lean.Elab.Tactic
