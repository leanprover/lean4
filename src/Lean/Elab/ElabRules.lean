/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.MacroArgUtil
import Lean.Elab.AuxDef

namespace Lean.Elab.Command
open Lean.Syntax
open Lean.Parser.Term hiding macroArg
open Lean.Parser.Command

def withExpectedType (expectedType? : Option Expr) (x : Expr → TermElabM Expr) : TermElabM Expr := do
  Term.tryPostponeIfNoneOrMVar expectedType?
  let some expectedType ← pure expectedType?
    | throwError "expected type must be known"
  x expectedType

def elabElabRulesAux (doc? : Option (TSyntax ``docComment))
    (attrs? : Option (TSepArray ``attrInstance ",")) (attrKind : TSyntax ``attrKind)
    (k : SyntaxNodeKind) (cat? expty? : Option (Ident)) (alts : Array (TSyntax ``matchAlt)) :
    CommandElabM Syntax := do
  let alts ← alts.mapM fun (alt : TSyntax ``matchAlt) => match alt with
    | `(matchAltExpr| | $pats,* => $rhs) => do
      let pat := pats.elemsAndSeps[0]!
      if !pat.isQuot then
        throwUnsupportedSyntax
      let quoted := getQuotContent pat
      let k' := quoted.getKind
      if checkRuleKind k' k then
        pure alt
      else if k' == choiceKind then
         match quoted.getArgs.find? fun quotAlt => checkRuleKind quotAlt.getKind k with
         | none        => throwErrorAt alt "invalid elab_rules alternative, expected syntax node kind '{k}'"
         | some quoted =>
           let pat := pat.setArg 1 quoted
           let pats := ⟨pats.elemsAndSeps.set! 0 pat⟩
           `(matchAltExpr| | $pats,* => $rhs)
      else
        throwErrorAt alt "invalid elab_rules alternative, unexpected syntax node kind '{k'}'"
    | _ => throwUnsupportedSyntax
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
  if let some expId := expty? then
    if catName == `term then
      `($[$doc?:docComment]? @[$(← mkAttrs `term_elab),*]
        aux_def elabRules $(mkIdent k) : Lean.Elab.Term.TermElab :=
        fun stx expectedType? => Lean.Elab.Command.withExpectedType expectedType? fun $expId => match stx with
          $alts:matchAlt* | _ => no_error_if_unused% throwUnsupportedSyntax)
    else
      throwErrorAt expId "syntax category '{catName}' does not support expected type specification"
  else if catName == `term then
    `($[$doc?:docComment]? @[$(← mkAttrs `term_elab),*]
      aux_def elabRules $(mkIdent k) : Lean.Elab.Term.TermElab :=
      fun stx _ => match stx with
        $alts:matchAlt* | _ => no_error_if_unused% throwUnsupportedSyntax)
  else if catName == `command then
    `($[$doc?:docComment]? @[$(← mkAttrs `command_elab),*]
      aux_def elabRules $(mkIdent k) : Lean.Elab.Command.CommandElab :=
      fun $alts:matchAlt* | _ => no_error_if_unused% throwUnsupportedSyntax)
  else if catName == `tactic || catName == `conv then
    `($[$doc?:docComment]? @[$(← mkAttrs `tactic),*]
      aux_def elabRules $(mkIdent k) : Lean.Elab.Tactic.Tactic :=
      fun $alts:matchAlt* | _ => no_error_if_unused% throwUnsupportedSyntax)
  else
    -- We considered making the command extensible and support new user-defined categories. We think it is unnecessary.
    -- If users want this feature, they add their own `elab_rules` macro that uses this one as a fallback.
    throwError "unsupported syntax category '{catName}'"

@[builtin_command_elab «elab_rules»] def elabElabRules : CommandElab :=
  adaptExpander fun stx => match stx with
  | `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind elab_rules $[: $cat?]? $[<= $expty?]? $alts:matchAlt*) =>
    expandNoKindMacroRulesAux alts "elab_rules" fun kind? alts =>
      `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind elab_rules $[(kind := $(mkIdent <$> kind?))]? $[: $cat?]? $[<= $expty?]? $alts:matchAlt*)
  | `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind elab_rules (kind := $kind) $[: $cat?]? $[<= $expty?]? $alts:matchAlt*) =>
    do elabElabRulesAux doc? attrs? attrKind (← resolveSyntaxKind kind.getId) cat? expty? alts
  | _  => throwUnsupportedSyntax

@[builtin_command_elab Lean.Parser.Command.elab]
def elabElab : CommandElab
  | `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind
    elab%$tk$[:$prec?]? $[(name := $name?)]? $[(priority := $prio?)]? $args:macroArg* :
      $cat $[<= $expectedType?]? => $rhs) => do
    let prio    ← liftMacroM <| evalOptPrio prio?
    let (stxParts, patArgs) := (← args.mapM expandMacroArg).unzip
    -- name
    let name ← match name? with
      | some name => pure name.getId
      | none => liftMacroM <| mkNameFromParserSyntax cat.getId (mkNullNode stxParts)
    let nameId := name?.getD (mkIdentFrom tk name (canonical := true))
    let pat := ⟨mkNode ((← getCurrNamespace) ++ name) patArgs⟩
    elabCommand <|← `(
      $[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind
      syntax%$tk$[:$prec?]? (name := $nameId) (priority := $(quote prio):num) $[$stxParts]* : $cat
      $[$doc?:docComment]? elab_rules : $cat $[<= $expectedType?]? | `($pat) => $rhs)
  | _ => throwUnsupportedSyntax

end Lean.Elab.Command
