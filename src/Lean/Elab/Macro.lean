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

@[builtin_command_elab Lean.Parser.Command.macro] def elabMacro : CommandElab
  | `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind
      macro%$tk$[:$prec?]? $[(name := $name?)]? $[(priority := $prio?)]? $args:macroArg* : $cat => $rhs) =>
    -- exclude command prefix from synthetic position used for e.g. jumping to the macro definition
    withRef (mkNullNode #[tk, rhs]) do
      let prio  ← liftMacroM <| evalOptPrio prio?
      let (stxParts, patArgs) := (← args.mapM expandMacroArg).unzip
      -- name
      let name ← match name? with
        | some name => pure name.getId
        | none => liftMacroM <| mkNameFromParserSyntax cat.getId (mkNullNode stxParts)
      /- The command `syntax [<kind>] ...` adds the current namespace to the syntax node kind.
        So, we must include current namespace when we create a pattern for the following `macro_rules` commands. -/
      let pat := ⟨mkNode ((← getCurrNamespace) ++ name) patArgs⟩
      let stxCmd ← `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind
        syntax$[:$prec?]?
          (name := $(name?.getD (mkIdentFrom tk name (canonical := true))))
          (priority := $(quote prio):num)
          $[$stxParts]* : $cat)
      let rhs := rhs.raw
      let macroRulesCmd ← if rhs.getArgs.size == 1 then
        -- `rhs` is a `term`
        let rhs := ⟨rhs[0]⟩
        `($[$doc?:docComment]? macro_rules | `($pat) => Functor.map (@TSyntax.raw $(quote cat.getId.eraseMacroScopes)) $rhs)
      else
        -- TODO(gabriel): remove after bootstrap
        -- `rhs` is of the form `` `( $body ) ``
        let rhsBody := ⟨rhs[1]⟩
        `($[$doc?:docComment]? macro_rules | `($pat) => `($rhsBody))
      elabCommand <| mkNullNode #[stxCmd, macroRulesCmd]
  | _ => throwUnsupportedSyntax

end Lean.Elab.Command
