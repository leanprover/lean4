/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lean.Elab.Eval
import Lean.Elab.ElabRules
import Lake.Util.FilePath
import Lake.DSL.Syntax

/-!
Syntax for elaboration time control flow.
-/

namespace Lake.DSL
open Lean Meta Elab Command Term

@[implemented_by Term.evalTerm]
opaque evalTerm (α) (type : Expr) (value : Syntax) (safety := DefinitionSafety.safe) : TermElabM α

def expandCmdDo : TSyntax ``cmdDo → Array Command
| `(cmdDo|do $cmds*) => cmds
| `(cmdDo|$cmd:command) => #[cmd]
| _ => #[]

@[builtin_command_elab metaIf]
def elabMetaIf : CommandElab := fun stx => do
  let `(meta if $c then $t $[else $e?]?) := stx
    | throwErrorAt stx "ill-formed meta if command"
  if (← withRef c <| runTermElabM fun _ => evalTerm Bool (toTypeExpr Bool) c .unsafe) then
    let cmd := mkNullNode (expandCmdDo t)
    withMacroExpansion (← getRef) cmd <| elabCommand cmd
  else if let some e := e? then
    let cmd := mkNullNode (expandCmdDo e)
    withMacroExpansion (← getRef) cmd <| elabCommand cmd

@[implemented_by Meta.evalExpr]
opaque evalExpr (α) (expectedType : Expr) (value : Expr) (safety := DefinitionSafety.safe) : MetaM α

def toExprIO [ToExpr α] (x : IO α) : IO Expr :=
  toExpr <$> x

@[builtin_term_elab runIO]
def elabRunIO : TermElab := fun stx expectedType? =>
  match stx with
  | `(run_io%$tk $t) => withRef t do
    let expectedType := mkApp (mkConst ``IO) <|
      expectedType?.getD <| ← mkFreshExprMVar <| mkSort <| .succ .zero
    let v ← elabTermEnsuringType (← `(do $t)) expectedType
    synthesizeSyntheticMVarsNoPostponing
    let v ← instantiateMVars v
    if (← logUnassignedUsingErrorInfos (← getMVars v)) then
      throwAbortTerm
    let v ← mkAppM ``toExprIO #[v]
    let io ← evalExpr (IO Expr) (mkApp (mkConst ``IO) (mkConst ``Expr)) v
    let (out, x) ← IO.FS.withIsolatedStreams io.toBaseIO
    unless out.isEmpty do
      logInfoAt tk out
    match x with
    | .ok x => return x
    | .error e => throwErrorAt tk e.toString
  | _ => Elab.throwUnsupportedSyntax
