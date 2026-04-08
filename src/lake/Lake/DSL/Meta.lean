/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lean.ToExpr
import Lean.Elab.Eval
import Lake.DSL.Syntax

/-!
Syntax for elaboration time control flow.
-/

open Lean Meta Elab Command Term

namespace Lake.DSL

def expandCmdDo : TSyntax ``cmdDo → Array Command
| `(cmdDo|do $cmds*) => cmds
| `(cmdDo|$cmd:command) => #[cmd]
| _ => #[]

@[builtin_command_elab metaIf]
def elabMetaIf : CommandElab := fun stx => do
  let `(meta if $c then $t $[else $e?]?) := stx
    | throwErrorAt stx "ill-formed meta if command"
  let c ← withRef c <| runTermElabM fun _ =>
    unsafe evalTerm Bool (toTypeExpr Bool) c .unsafe
  if c then
    let cmd := mkNullNode (expandCmdDo t)
    withMacroExpansion (← getRef) cmd <| elabCommand cmd
  else if let some e := e? then
    let cmd := mkNullNode (expandCmdDo e)
    withMacroExpansion (← getRef) cmd <| elabCommand cmd

public def toExprIO [ToExpr α] (x : IO α) : IO Expr :=
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
    let io ← unsafe evalExpr (IO Expr) (mkApp (mkConst ``IO) (mkConst ``Expr)) v
    let (out, x) ← IO.FS.withIsolatedStreams io.toBaseIO
    unless out.isEmpty do
      logInfoAt tk out
    match x with
    | .ok x => return x
    | .error e => throwErrorAt tk e.toString
  | _ => Elab.throwUnsupportedSyntax
