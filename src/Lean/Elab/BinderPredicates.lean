/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
module

prelude
public import Lean.Elab.MacroArgUtil
public import Lean.Linter.MissingDocs

public section

namespace Lean.Elab.Command

@[builtin_command_elab binderPredicate] def elabBinderPred : CommandElab := fun stx => do
  match stx with
  | `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind binder_predicate%$tk
      $[(name := $name?)]? $[(priority := $prio?)]? $x $args:macroArg* => $rhs) => do
    let prio ← liftMacroM do evalOptPrio prio?
    let (stxParts, patArgs) := (← args.mapM expandMacroArg).unzip
    let kind ← elabSyntax (← `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind syntax%$tk
        $[(name := $name?)]? (priority := $(quote prio)) $[$stxParts]* : binderPred))
    /- The command `syntax [<kind>] ...` adds the current namespace to the syntax node kind.
    So, we must include current namespace when we create a pattern for the following
    `macro_rules` commands. -/
    let pat : TSyntax `binderPred := ⟨(mkNode kind patArgs).1⟩
    elabCommand <|<-
    `($[$doc?:docComment]? macro_rules%$tk
        | `(satisfies_binder_pred% $$($x):term $pat:binderPred) => $rhs)
  | _ => throwUnsupportedSyntax

open Linter.MissingDocs Parser Term in
/-- Missing docs handler for `binder_predicate` -/
@[builtin_missing_docs_handler Lean.Parser.Command.binderPredicate]
def checkBinderPredicate : SimpleHandler := fun stx => do
  if stx[0].isNone && stx[2][0][0].getKind != ``«local» then
    if stx[4].isNone then lint stx[3] "binder predicate"
    else lintNamed stx[4][0][3] "binder predicate"

end Lean.Elab.Command
