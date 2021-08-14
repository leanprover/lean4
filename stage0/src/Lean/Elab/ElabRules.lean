/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.MacroArgUtil

namespace Lean.Elab.Command
open Lean.Syntax
open Lean.Parser.Term hiding macroArg

def withExpectedType (expectedType? : Option Expr) (x : Expr → TermElabM Expr) : TermElabM Expr := do
  Term.tryPostponeIfNoneOrMVar expectedType?
  let some expectedType ← pure expectedType?
    | throwError "expected type must be known"
  x expectedType

def elabElabRulesAux (doc? : Option Syntax) (attrKind : Syntax) (k : SyntaxNodeKind) (cat? expty? : Option Syntax) (alts : Array Syntax) : CommandElabM Syntax := do
  let alts ← alts.mapM fun alt => match alt with
    | `(matchAltExpr| | $pats,* => $rhs) => do
      let pat := pats.elemsAndSeps[0]
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
           let pats := pats.elemsAndSeps.set! 0 pat
           `(matchAltExpr| | $pats,* => $rhs)
      else
        throwErrorAt alt "invalid elab_rules alternative, unexpected syntax node kind '{k'}'"
    | _ => throwUnsupportedSyntax
  let catName ← match cat?, expty? with
    | some cat, _ => cat.getId
    | _, some _   => `term
    -- TODO: infer category from quotation kind, possibly even kind of quoted syntax?
    | _, _        => throwError "invalid elab_rules command, specify category using `elab_rules : <cat> ...`"
  if let some expId := expty? then
    if catName == `term then
      `($[$doc?:docComment]? @[termElab $(← mkIdentFromRef k):ident] def elabFn : Lean.Elab.Term.TermElab :=
        fun stx expectedType? => Lean.Elab.Command.withExpectedType expectedType? fun $expId => match stx with
          $alts:matchAlt* | _ => throwUnsupportedSyntax)
    else
      throwErrorAt expId "syntax category '{catName}' does not support expected type specification"
  else if catName == `term then
    `($[$doc?:docComment]? @[termElab $(← mkIdentFromRef k):ident] def elabFn : Lean.Elab.Term.TermElab :=
      fun stx _ => match stx with
        $alts:matchAlt* | _ => throwUnsupportedSyntax)
  else if catName == `command then
    `($[$doc?:docComment]? @[commandElab $(← mkIdentFromRef k):ident] def elabFn : Lean.Elab.Command.CommandElab :=
      fun $alts:matchAlt* | _ => throwUnsupportedSyntax)
  else if catName == `tactic then
    `($[$doc?:docComment]? @[tactic $(← mkIdentFromRef k):ident] def elabFn : Lean.Elab.Tactic.Tactic :=
      fun $alts:matchAlt* | _ => throwUnsupportedSyntax)
  else
    -- We considered making the command extensible and support new user-defined categories. We think it is unnecessary.
    -- If users want this feature, they add their own `elab_rules` macro that uses this one as a fallback.
    throwError "unsupported syntax category '{catName}'"

@[builtinCommandElab «elab_rules»] def elabElabRules : CommandElab :=
  adaptExpander fun stx => match stx with
  | `($[$doc?:docComment]? $attrKind:attrKind elab_rules $[: $cat?]? $[<= $expty?]? $alts:matchAlt*) =>
    expandNoKindMacroRulesAux alts "elab_rules" fun kind? alts =>
      `($[$doc?:docComment]? $attrKind:attrKind elab_rules $[(kind := $(mkIdent <$> kind?))]? $[: $cat?]? $[<= $expty?]? $alts:matchAlt*)
  | `($[$doc?:docComment]? $attrKind:attrKind elab_rules (kind := $kind) $[: $cat?]? $[<= $expty?]? $alts:matchAlt*) =>
    do elabElabRulesAux doc? attrKind (← resolveSyntaxKind kind.getId) cat? expty? alts
  | _  => throwUnsupportedSyntax

@[builtinMacro Lean.Parser.Command.elab]
def expandElab : Macro
  | `($[$doc?:docComment]? $attrKind:attrKind
    elab$[:$prec?]? $[(name := $name?)]? $[(priority := $prio?)]? $args:macroArg* :
      $cat $[<= $expectedType?]? => $rhs) => do
    let prio    ← evalOptPrio prio?
    let catName := cat.getId
    let (stxParts, patArgs) := (← args.mapM expandMacroArg).unzip
    -- name
    let name ← match name? with
      | some name => pure name.getId
      | none => mkNameFromParserSyntax cat.getId (mkNullNode stxParts)
    let pat := Syntax.node ((← Macro.getCurrNamespace) ++ name) patArgs
    `($[$doc?:docComment]? $attrKind:attrKind syntax$[:$prec?]? (name := $(← mkIdentFromRef name)) (priority := $(quote prio)) $[$stxParts]* : $cat
      $[$doc?:docComment]? elab_rules : $cat $[<= $expectedType?]? | `($pat) => $rhs)
  | _ => Macro.throwUnsupported

end Lean.Elab.Command
