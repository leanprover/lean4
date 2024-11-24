/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Lean.Elab.SyntheticMVars
import Lean.Elab.Command
import Lean.Meta.Tactic.Unfold
import Lean.Meta.Eval
import Lean.Compiler.ImplementedByAttr

open Lean Elab Meta Command Term Compiler

syntax (name := testExternCmd) "test_extern " term : command

@[command_elab testExternCmd] unsafe def elabTestExtern : CommandElab
  | `(test_extern $t:term) => liftTermElabM do
    let t ← elabTermAndSynthesize t none
    match t.getAppFn with
    | .const f _ =>
      let env ← getEnv
      if isExtern env f || (getImplementedBy? env f).isSome then
        let t' := (← unfold t f).expr
        let r := mkApp (.const ``reduceBool []) (← mkDecide (← mkEq t t'))
        if ! (← evalExpr Bool (.const ``Bool []) r) then
          throwError
            ("native implementation did not agree with reference implementation!\n" ++
            m!"Compare the outputs of:\n#eval {t}\n and\n#eval {t'}")
      else
        throwError "test_extern: {f} does not have an @[extern] attribute or @[implemented_by] attribute"
    | _ => throwError "test_extern: expects a function application"
  | _ => throwUnsupportedSyntax
