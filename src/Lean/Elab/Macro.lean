/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.MacroArgUtil

namespace Lean.Elab.Command
open Lean.Syntax
open Lean.Parser.Term hiding macroArg
open Lean.Parser.Command

@[builtinCommandElab Lean.Parser.Command.macro] def elabMacro : CommandElab
  | `($[$doc?:docComment]? $attrKind:attrKind
      macro%$tk$[:$prec?]? $[(name := $name?)]? $[(priority := $prio?)]? $args:macroArg* :
        $cat => $rhs) => do
    let prio  ← liftMacroM <| evalOptPrio prio?
    let (stxParts, patArgs) := (← args.mapM expandMacroArg).unzip
    -- name
    let name ← match name? with
      | some name => pure name.getId
      | none => liftMacroM <| mkNameFromParserSyntax cat.getId (mkNullNode stxParts)
    /- The command `syntax [<kind>] ...` adds the current namespace to the syntax node kind.
      So, we must include current namespace when we create a pattern for the following `macro_rules` commands. -/
    let pat := ⟨mkNode ((← getCurrNamespace) ++ name) patArgs⟩
    let stxCmd ← `($[$doc?:docComment]? $attrKind:attrKind
      syntax%$tk$[:$prec?]? (name := $(← mkIdentFromRef name)) (priority := $(quote prio):num) $[$stxParts]* : $cat)
    let rhs := rhs.raw
    let macroRulesCmd ← if rhs.getArgs.size == 1 then
      -- `rhs` is a `term`
      let rhs := ⟨rhs[0]⟩
      `($[$doc?:docComment]? macro_rules%$tk | `($pat) => $rhs)
    else
      -- `rhs` is of the form `` `( $body ) ``
      let rhsBody := ⟨rhs[1]⟩
      `($[$doc?:docComment]? macro_rules%$tk | `($pat) => `($rhsBody))
    elabCommand <| mkNullNode #[stxCmd, macroRulesCmd]
  | _ => throwUnsupportedSyntax

end Lean.Elab.Command
