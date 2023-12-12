/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Elab.Eval
import Lean.Elab.ElabRules

/-!
Syntax for elaboration time control flow.
-/

namespace Lake.DSL
open Lean Meta Elab Command Term

@[implemented_by Term.evalTerm]
opaque evalTerm (α) (type : Expr) (value : Syntax) (safety := DefinitionSafety.safe) : TermElabM α

/--
The `do` command syntax groups multiple similarly indented commands together.
The group can then be passed to another command that usually only accepts a
single command (e.g., `meta if`).
-/
syntax cmdDo := ("do" many1Indent(command)) <|> command

def expandCmdDo : TSyntax ``cmdDo → Array Command
| `(cmdDo|do $cmds*) => cmds
| `(cmdDo|$cmd:command) => #[cmd]
| _ => #[]

/--
The `meta if` command has two forms:

```lean
meta if <c:term> then <a:command>
meta if <c:term> then <a:command> else <b:command>
```

It expands to the command `a` if the term `c` evaluates to true
(at elaboration time). Otherwise, it expands to command `b` (if an `else`
clause is provided).

One can use this command to specify, for example, external library targets
only available on specific platforms:

```lean
meta if System.Platform.isWindows then
extern_lib winOnlyLib := ...
else meta if System.Platform.isOSX then
extern_lib macOnlyLib := ...
else
extern_lib linuxOnlyLib := ...
```
-/
scoped syntax (name := metaIf)
"meta " "if " term " then " cmdDo (" else " cmdDo)? : command

elab_rules : command | `(meta if $c then $t $[else $e?]?) => do
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

/--
Executes a term of type `IO α` at elaboration-time
and produces an expression corresponding to the result via `ToExpr α`.
-/
scoped syntax:lead (name := runIO) "run_io " doSeq : term

@[term_elab runIO]
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

/-! ## ToExpr Instances -/

instance : ToExpr System.FilePath where
  toExpr p := mkApp (mkConst ``System.FilePath.mk) (toExpr p.toString)
  toTypeExpr := mkConst ``System.FilePath

