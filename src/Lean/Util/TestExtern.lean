import Lean.Elab.SyntheticMVars
import Lean.Elab.Command
import Lean.Meta.Tactic.Unfold
import Lean.Meta.Eval

open Lean Elab Meta Command Term

syntax (name := testExternCmd) "test_extern " term : command

@[command_elab testExternCmd] unsafe def elabTestExtern : CommandElab
  | `(test_extern $t:term) => liftTermElabM do
    let t ← elabTermAndSynthesize t none
    match t.getAppFn with
    | .const f _ =>
      if isExtern (← getEnv) f then
        let t' := (← unfold t f).expr
        let r := mkApp (.const ``reduceBool []) (← mkAppM ``BEq.beq #[t, t'])
        if ! (← evalExpr Bool (.const ``Bool []) r) then
          throwError
            ("native implementation did not agree with reference implementation!\n" ++
            m!"Compare the outputs of:\n#eval {t}\n and\n#eval {t'}")
      else
        throwError "test_extern: {f} does not have an @[extern] attribute"
    | _ => throwError "test_extern: expects a function application"
  | _ => throwUnsupportedSyntax
