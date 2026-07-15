/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Elab.MacroArgUtil

public section

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
      let kind ← elabSyntax (← `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind
        syntax$[:$prec?]?
          $[(name := $name?)]?
          (priority := $(quote prio):num)
          $[$stxParts]* : $cat))
      let pat := ⟨mkNode kind patArgs⟩
      let rhs := rhs.raw
      -- Elide `scoped` for `macro_rules`; this allows for using scoped macros in unscoped macros
      -- for back-compat and unlike with `local`, there would be no benefit to enforcing `scoped`.
      let mut rulesKind := attrKind
      if rulesKind matches `(attrKind| scoped) then
        rulesKind ← `(attrKind| )
      let macroRulesCmd ← if rhs.getArgs.size == 1 then
        -- `rhs` is a `term`
        let rhs := ⟨rhs[0]⟩
        `($[$doc?:docComment]? $rulesKind:attrKind macro_rules | `($pat) => Functor.map (@TSyntax.raw $(quote cat.getId.eraseMacroScopes)) $rhs)
      else
        -- TODO(gabriel): remove after bootstrap
        -- `rhs` is of the form `` `( $body ) ``
        let rhsBody := ⟨rhs[1]⟩
        `($[$doc?:docComment]? $rulesKind:attrKind macro_rules | `($pat) => `($rhsBody))
      elabCommand macroRulesCmd
  | _ => throwUnsupportedSyntax

end Lean.Elab.Command
