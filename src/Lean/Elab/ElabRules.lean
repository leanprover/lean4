/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Elab.MacroArgUtil
public import Lean.Elab.AuxDef
public import Lean.Elab.Do.Basic

public section

namespace Lean.Elab.Command
open Lean.Syntax
open Lean.Parser.Term hiding macroArg
open Lean.Parser.Command

def elabElabRulesAux (doc? : Option (TSyntax ``docComment))
    (attrs? : Option (TSepArray ``attrInstance ",")) (attrKind : TSyntax ``attrKind)
    (k : SyntaxNodeKind) (cat? expty? : Option (Ident)) (alts : Array (TSyntax ``matchAlt)) :
    CommandElabM Syntax := do
  let alts ← alts.mapM (checkRuleAltKind "elab_rules" k)
  let catName ← match cat?, expty? with
    | some cat, _ => pure cat.getId
    | _, some _   => pure `term
    -- TODO: infer category from quotation kind, possibly even kind of quoted syntax?
    | _, _        => throwError "invalid elab_rules command, specify category using `elab_rules : <cat> ...`"
  let mkAttrs (kind : Name) : CommandElabM (TSyntaxArray ``attrInstance) := do
    let attr ← `(attrInstance| $attrKind:attrKind $(mkIdent kind):ident $(← mkIdentFromRef k):ident)
    pure <| match attrs? with
      | some attrs => attrs.getElems.push attr
      | none => #[attr]
  let vis := Parser.Command.visibility.ofAttrKind attrKind
  if let some expId := expty? then
    if catName == `term then
      `($[$doc?:docComment]? @[$(← mkAttrs `term_elab),*] $vis:visibility
        aux_def elabRules $(mkIdent k) : Lean.Elab.Term.TermElab :=
        fun stx expectedType? => Lean.Elab.Term.withExpectedType expectedType? fun $expId => match stx with
          $alts:matchAlt* | _ => no_error_if_unused% throwUnsupportedSyntax)
    else if catName == `doElem then
      `($[$doc?:docComment]? @[$(← mkAttrs `doElem_elab),*] $vis:visibility
        aux_def elabRules $(mkIdent k) : Lean.Elab.Do.DoElab :=
        fun stx $expId => match stx with
          $alts:matchAlt* | _ => no_error_if_unused% throwUnsupportedSyntax)
    else
      throwErrorAt expId "syntax category `{catName}` does not support expected type specification"
  else if catName == `term then
    `($[$doc?:docComment]? @[$(← mkAttrs `term_elab),*] $vis:visibility
      aux_def elabRules $(mkIdent k) : Lean.Elab.Term.TermElab :=
      fun stx _ => match stx with
        $alts:matchAlt* | _ => no_error_if_unused% throwUnsupportedSyntax)
  else if catName == `command then
    `($[$doc?:docComment]? @[$(← mkAttrs `command_elab),*] $vis:visibility
      aux_def elabRules $(mkIdent k) : Lean.Elab.Command.CommandElab :=
      fun $alts:matchAlt* | _ => no_error_if_unused% throwUnsupportedSyntax)
  else if catName == `tactic || catName == `conv then
    `($[$doc?:docComment]? @[$(← mkAttrs `tactic),*] $vis:visibility
      aux_def elabRules $(mkIdent k) : Lean.Elab.Tactic.Tactic :=
      fun $alts:matchAlt* | _ => no_error_if_unused% throwUnsupportedSyntax)
  else if catName == `doElem then
    `($[$doc?:docComment]? @[$(← mkAttrs `doElem_elab),*] $vis:visibility
      aux_def elabRules $(mkIdent k) : Lean.Elab.Do.DoElab :=
      fun stx cont => match stx with
        $alts:matchAlt* | _ => no_error_if_unused% throwUnsupportedSyntax)
  else
    -- We considered making the command extensible and support new user-defined categories. We think it is unnecessary.
    -- If users want this feature, they add their own `elab_rules` macro that uses this one as a fallback.
    throwError "unsupported syntax category `{catName}`"

@[builtin_command_elab «elab_rules»] def elabElabRules : CommandElab :=
  adaptRulesExpander fun stx => match stx with
  | `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind elab_rules $[: $cat?]? $[<= $expty?]? $alts:matchAlt*) =>
    return (none, ← expandNoKindMacroRulesAux alts "elab_rules" fun kind? alts =>
      `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind elab_rules $[(kind := $(mkIdent <$> kind?))]? $[: $cat?]? $[<= $expty?]? $alts:matchAlt*))
  | `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind elab_rules (kind := $kind) $[: $cat?]? $[<= $expty?]? $alts:matchAlt*) => do
    let k ← resolveSyntaxKind kind.getId
    return (k, ← elabElabRulesAux doc? attrs? attrKind k cat? expty? alts)
  | _  => throwUnsupportedSyntax

@[builtin_command_elab Lean.Parser.Command.elab]
def elabElab : CommandElab
  | `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind
    elab%$tk$[:$prec?]? $[(name := $name?)]? $[(priority := $prio?)]? $args:macroArg* :
      $cat $[<= $expectedType?]? => $rhs) => do
    let prio    ← liftMacroM <| evalOptPrio prio?
    let (stxParts, patArgs) := (← args.mapM expandMacroArg).unzip
    let kind ← elabSyntax <|← `(
      $[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind
      syntax%$tk$[:$prec?]? $[(name := $name?)]? (priority := $(quote prio):num) $[$stxParts]* : $cat)
    let pat := ⟨mkNode kind patArgs⟩
    elabCommand <|← `(
      $[$doc?:docComment]? elab_rules : $cat $[<= $expectedType?]? | `($pat) => $rhs)
  | _ => throwUnsupportedSyntax

end Lean.Elab.Command
