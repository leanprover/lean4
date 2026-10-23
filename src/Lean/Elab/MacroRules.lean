/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Elab.Syntax
public import Lean.Elab.AuxDef

public section

namespace Lean.Elab.Command
open Lean.Syntax
open Lean.Parser.Term hiding macroArg
open Lean.Parser.Command

/--
Returns a `Macro` that runs the right-hand side of the first alternative in `alts` whose pattern
matches, and throws `Macro.Exception.unsupportedSyntax` if there is none. Checks that the patterns
are quotations of syntax of kind `k`, naming the command `cmdName` in errors.
-/
def mkMacroRulesFun (cmdName : String) (k : SyntaxNodeKind) (alts : Array (TSyntax ``matchAlt)) :
    CommandElabM Term := do
  let alts ← alts.mapM (checkRuleAltKind cmdName k)
  `(fun $alts:matchAlt* | _ => no_error_if_unused% throw Lean.Macro.Exception.unsupportedSyntax)

/--
  Remark: `k` is the user provided kind with the current namespace included.
  Recall that syntax node kinds contain the current namespace.
-/
def elabMacroRulesAux (doc? : Option (TSyntax ``docComment))
    (attrs? : Option (TSepArray ``attrInstance ",")) (attrKind : TSyntax ``attrKind)
    (tk : Syntax) (k : SyntaxNodeKind) (alts : Array (TSyntax ``matchAlt)) :
    CommandElabM Syntax := do
  let body ← mkMacroRulesFun "macro_rules" k alts
  let attr ← `(attrInstance| $attrKind macro $(Lean.mkIdent k))
  let attrs := match attrs? with
    | some attrs => attrs.getElems.push attr
    | none => #[attr]
  let vis := Parser.Command.visibility.ofAttrKind attrKind
  `($[$doc?:docComment]? @[$attrs,*] $vis:visibility
    aux_def macroRules $(mkIdentFrom tk k (canonical := true)) : Macro := $body)

@[builtin_command_elab «macro_rules»] def elabMacroRules : CommandElab :=
  adaptRulesExpander fun stx => match stx with
  | `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind macro_rules%$tk $alts:matchAlt*) =>
    -- exclude command prefix from synthetic position used for e.g. jumping to the macro definition
    withRef (mkNullNode #[tk, mkNullNode alts]) do
      return (none, ← expandNoKindMacroRulesAux alts "macro_rules" fun kind? alts =>
        `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind macro_rules $[(kind := $(mkIdent <$> kind?))]? $alts:matchAlt*))
  | `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind macro_rules%$tk (kind := $kind) | $x:ident => $rhs) =>
    withRef (mkNullNode #[tk, rhs]) do
      let attr ← `(attrInstance| $attrKind:attrKind macro $kind)
      let attrs := match attrs? with
        | some attrs => attrs.getElems.push attr
        | none => #[attr]
      let vis := Parser.Command.visibility.ofAttrKind attrKind
      -- An invalid kind is reported by the `macro` attribute
      let k? ← (some <$> resolveSyntaxKind kind.getId) <|> pure none
      return (k?, ← `($[$doc?:docComment]? @[$attrs,*] $vis:visibility
        aux_def $(mkIdentFrom tk kind.getId (canonical := true)) $kind : Macro := fun $x:ident => $rhs))
  | `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind macro_rules%$tk (kind := $kind) $alts:matchAlt*) =>
    withExporting (isExporting := !attrKind matches `(attrKind| local)) do
    withRef (mkNullNode #[tk, mkNullNode alts]) do
      let k ← resolveSyntaxKind kind.getId
      return (k, ← elabMacroRulesAux doc? attrs? attrKind tk k alts)
  | _  => throwUnsupportedSyntax

end Lean.Elab.Command
