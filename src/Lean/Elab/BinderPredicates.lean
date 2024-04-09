/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
prelude
import Init.BinderPredicates
import Lean.Parser.Syntax
import Lean.Elab.MacroArgUtil
import Lean.Linter.MissingDocs

namespace Lean.Elab.Command

@[builtin_command_elab binderPredicate] def elabBinderPred : CommandElab := fun stx => do
  match stx with
  | `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind binder_predicate%$tk
      $[(name := $name?)]? $[(priority := $prio?)]? $x $args:macroArg* => $rhs) => do
    let prio ← liftMacroM do evalOptPrio prio?
    let (stxParts, patArgs) := (← args.mapM expandMacroArg).unzip
    let name ← match name? with
      | some name => pure name.getId
      | none => liftMacroM do mkNameFromParserSyntax `binderTerm (mkNullNode stxParts)
    let nameTk := name?.getD (mkIdentFrom tk name)
    /- The command `syntax [<kind>] ...` adds the current namespace to the syntax node kind.
    So, we must include current namespace when we create a pattern for the following
    `macro_rules` commands. -/
    let pat : TSyntax `binderPred := ⟨(mkNode ((← getCurrNamespace) ++ name) patArgs).1⟩
    elabCommand <|<-
    `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind syntax%$tk
        (name := $nameTk) (priority := $(quote prio)) $[$stxParts]* : binderPred
      $[$doc?:docComment]? macro_rules%$tk
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
