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

@[builtinMacro Lean.Parser.Command.macro] def expandMacro : Macro
  | `($[$doc?:docComment]? $attrKind:attrKind
      macro$[:$prec?]? $[(name := $name?)]? $[(priority := $prio?)]? $args:macroArg* :
        $cat => $rhs) => do
    let prio  ← evalOptPrio prio?
    let (stxParts, patArgs) := (← args.mapM expandMacroArg).unzip
    -- name
    let name ← match name? with
      | some name => pure name.getId
      | none => mkNameFromParserSyntax cat.getId (mkNullNode stxParts)
    /- The command `syntax [<kind>] ...` adds the current namespace to the syntax node kind.
      So, we must include current namespace when we create a pattern for the following `macro_rules` commands. -/
    let pat := Syntax.node ((← Macro.getCurrNamespace) ++ name) patArgs
    let stxCmd ← `($[$doc?:docComment]? $attrKind:attrKind
      syntax$[:$prec?]? (name := $(← mkIdentFromRef name)) (priority := $(quote prio)) $[$stxParts]* : $cat)
    let macroRulesCmd ←
      if rhs.getArgs.size == 1 then
        -- `rhs` is a `term`
        let rhs := rhs[0]
        `($[$doc?:docComment]? macro_rules | `($pat) => $rhs)
      else
        -- `rhs` is of the form `` `( $body ) ``
        let rhsBody := rhs[1]
        `($[$doc?:docComment]? macro_rules | `($pat) => `($rhsBody))
    return mkNullNode #[stxCmd, macroRulesCmd]
  | _ => Macro.throwUnsupported

end Lean.Elab.Command
