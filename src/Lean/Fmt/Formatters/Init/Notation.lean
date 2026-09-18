/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
import Lean.Fmt.Formatters.Lean.Parser.Term
meta import Init.Notation
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt «prec(_)»]
public def fmtPrecParen : Fmt := fun
  | `(prec| (%$lbTk $prec:prec )%$rbTk ) => do
    let lbTk ← fmt lbTk
    let prec ← fmt prec
    let rbTk ← fmt rbTk
    return Layouts.parens lbTk prec rbTk
  | _ =>
    throw .partialFormatter

@[builtin_infix_fmt Lean.Parser.Syntax.addPrec]
public def fmtAddPrec : Fmt.InfixOperation := {
  sparse := false
  precs? := some { prec := 65, lhsPrec := 0, rhsPrec := 66 }
}

@[builtin_infix_fmt Lean.Parser.Syntax.subPrec]
public def fmtSubPrec : Fmt.InfixOperation := {
  sparse := false
  precs? := some { prec := 65, lhsPrec := 0, rhsPrec := 66 }
}

@[builtin_infix_fmt Lean.Parser.Syntax.addPrio]
public def fmtAddPrio : Fmt.InfixOperation := {
  sparse := false
  precs? := some { prec := 65, lhsPrec := 0, rhsPrec := 66 }
}

@[builtin_infix_fmt Lean.Parser.Syntax.subPrio]
public def fmtSubPrio : Fmt.InfixOperation := {
  sparse := false
  precs? := some { prec := 65, lhsPrec := 0, rhsPrec := 66 }
}

@[builtin_fmt «prio(_)»]
public def fmtPrioParen : Fmt := fun
  | `(prio| (%$lbTk $prio:prio )%$rbTk ) => do
    let lbTk ← fmt lbTk
    let prio ← fmt prio
    let rbTk ← fmt rbTk
    return Layouts.parens lbTk prio rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt «stx_+», builtin_fmt «stx_*», builtin_fmt «stx_,*», builtin_fmt «stx_,+»,
  builtin_fmt «stx_,*,?», builtin_fmt «stx_,+,?»]
public def fmtStxPostfix : Fmt := fmtPostfixOperator

private inductive EndsInIdent where
  | empty
  | endsInNonIdent
  | endsInIdent
deriving Inhabited

instance : Max EndsInIdent where
  max a b :=
    if prio a >= prio b then
      a
    else
      b
where
  prio : EndsInIdent → Nat
    | .empty => 0
    | .endsInNonIdent => 2
    | .endsInIdent => 1

@[builtin_fmt stx_?]
public partial def fmtStxOptional : Fmt := fun stx => do
  if stx.getNumArgs != 2 then
    throw .partialFormatter
  let operand ← getStxArg! stx 0
  let questionTk ← getStxArg! stx 1
  let endsInId := endsInIdent operand
  let operand ← fmt operand
  let questionTk ← fmt questionTk
  let format := if endsInId matches .endsInIdent then .withSpacing else .withoutSpacing
  return Layouts.postfixOperator operand questionTk format
where
  endsInIdent : Syntax → EndsInIdent
    | .missing =>
      .empty
    | .atom .. =>
      .endsInNonIdent
    | .ident .. =>
      .endsInIdent
    | .node _ kind args =>
      if args.isEmpty then
        .empty
      else if kind == choiceKind then
        args.map endsInIdent |>.max?.getD .empty
      else
        args.map endsInIdent |>.filter (! · matches .empty) |>.back?.getD .empty

@[builtin_fmt stx!_]
public def fmtStxNotFollowedBy : Fmt := fun
  | `(stx!_| !%$notTk$s:stx) => do
    let notTk ← fmt notTk
    let s ← fmt s
    return Layouts.prefixOperator notTk s .withoutSpacingIfAtomic
  | _ =>
    throw .partialFormatter

@[builtin_infix_fmt «stx_<|>_»]
public def fmtStxOrelse : Fmt.InfixOperation := {
  sparse := false
  precs? := some { prec := 2, lhsPrec := 2, rhsPrec := 1 }
}

@[builtin_fmt «term¬_», builtin_fmt term!_]
public def fmtTermNot : Fmt := fmtPrefixOperator

@[builtin_fmt «term-_»]
public def fmtTermNeg : Fmt := fun
  | `(-%$negTk $num:num) => do
    let negTk ← fmt negTk
    let num ← fmt num
    return Layouts.prefixOperator negTk num .withoutSpacing
  | `(-%$negTk $t) => do
    let negTk ← fmt negTk
    let t ← fmt t
    return Layouts.prefixOperator negTk t .withoutSpacingIfAtomic
  | _ =>
    throw .partialFormatter

@[builtin_fmt «term_⁻¹»]
public def fmtTermInv : Fmt := fun
  | `($t⁻¹%$invTk) => do
    let t ← fmt t
    let invTk ← fmt invTk
    return mkSelfDelimited <| Layouts.postfixOperator t invTk .withoutSpacing
  | _ =>
    throw .partialFormatter

@[builtin_infix_fmt «term_∈_»]
public def fmtTermMem : Fmt.InfixOperation := {
  sparse := false
  precs? := some { prec := 50, lhsPrec := 50, rhsPrec := 50 }
}

@[builtin_infix_fmt «term_∉_»]
public def fmtTermNotMem : Fmt.InfixOperation := {
  sparse := false
  precs? := some { prec := 50, lhsPrec := 50, rhsPrec := 50 }
}

@[builtin_infix_fmt «term_≤_»]
public def fmtTermLe : Fmt.InfixOperation := {
  sparse := true
  precs? := some { prec := 50, lhsPrec := 51, rhsPrec := 51 }
}

@[builtin_infix_fmt «term_≥_»]
public def fmtTermGe : Fmt.InfixOperation := {
  sparse := true
  precs? := some { prec := 50, lhsPrec := 51, rhsPrec := 51 }
}

@[builtin_infix_fmt «term_∧_»]
public def fmtTermAnd : Fmt.InfixOperation := {
  sparse := false
  precs? := some { prec := 35, lhsPrec := 36, rhsPrec := 35 }
}

@[builtin_infix_fmt «term_∨_»]
public def fmtTermOr : Fmt.InfixOperation := {
  sparse := false
  precs? := some { prec := 30, lhsPrec := 31, rhsPrec := 30 }
}

public structure PipeOperator where
  lhs : Syntax
  pipeTk : Syntax
  rhs : Syntax

public def fmtPipeOperator (deconstruct? : Syntax → Option PipeOperator) : Fmt := fun stx => do
  let mut stx := stx
  let mut chain := #[]
  while true do
    let some pipeOp := deconstruct? stx
      | break
    chain := chain.push <| ← fmt pipeOp.lhs
    chain := chain.push <| ← fmt pipeOp.pipeTk
    stx := pipeOp.rhs
  if chain.isEmpty then
    throw .partialFormatter
  chain := chain.push <| ← fmt stx
  return Layouts.pipeOperator chain

@[builtin_fmt «term_<|_»]
public def fmtTermPipeLeft : Fmt :=
  fmtPipeOperator fun
    | `(term| $lhs:term <|%$pipeTk $rhs:term) => some ⟨lhs, pipeTk, rhs⟩
    | _ => none

@[builtin_fmt «term_|>_»]
public def fmtTermPipeRight : Fmt := fun stx =>
  fmtPipeProjLike stx fun
    | `($lhs:term |>%$pipeTk $rhs:term) => do
      let pipeTk ← fmt pipeTk
      let rhs ← fmt rhs
      let pipe := Layouts.prefixOperator pipeTk rhs .withSpacing
      return some (lhs, pipe)
    | stx =>
      deconstructPipeProj stx

@[builtin_fmt «term_$__»]
public def fmtTermDollar : Fmt :=
  fmtPipeOperator fun
    | `(term| $lhs:term $%$dollarTk $rhs:term) => some ⟨lhs, dollarTk, rhs⟩
    | _ => none

@[builtin_fmt rawNatLit]
public def fmtRawNatLit : Fmt := fun
  | `(rawNatLit| nat_lit%$natLitTk $n:num) => do fmtAppLike #[natLitTk, n]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.binderIdent]
public def fmtBinderIdent : Fmt := fun
  | `(binderIdent| _%$holeTk) => fmt holeTk
  | `(binderIdent| $id:ident) => fmt id
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.caseArg]
public def fmtCaseArg : Fmt := fun
  | `(Parser.Tactic.caseArg| $tag:binderIdent $ids:binderIdent*) => do
    let tag ← fmt tag
    let ids ← fmtArray ids
    return Layouts.pseudoApplication <| #[tag] ++ ids
  | _ =>
    throw .partialFormatter

@[builtin_conditional_fmt termIfThenElse]
public def fmtIfThenElse : ConditionalFmt := fun
  | `(termIfThenElse| if%$ifTk $cond:term then%$thenTk $thenBody:term else%$elseTk $elseBody:term) =>
    do
      let cond ← fmt cond
      return some { ifTk, cond, thenTk, thenBody, elseTk? := elseTk, elseBody? := elseBody }
  | _ =>
    pure none

@[builtin_conditional_fmt termDepIfThenElse]
public def fmtDepIfThenElse : ConditionalFmt := fun
  | `(termDepIfThenElse|
      if%$ifTk $h:binderIdent :%$colonTk $c:term then%$thenTk $thenBody:term else%$elseTk $elseBody:term) =>
    do
      let h ← fmt h
      let colonTk ← fmt colonTk
      let c ← fmt c
      let cond := Layouts.typeAscription h colonTk c
      return some { ifTk, cond, thenTk, thenBody, elseTk? := elseTk, elseBody? := elseBody }
  | _ =>
    pure none

@[builtin_conditional_fmt termIfLet]
public def fmtIfLet : ConditionalFmt := fun
  | `(termIfLet|
      if%$ifTk let%$letTk $pat:term :=%$colonEqTk $d:term then%$thenTk $thenBody:term else%$elseTk $elseBody:term) =>
    do
      let letTk ← fmt letTk
      let pat ← fmt pat
      let colonEqTk ← fmt colonEqTk
      let d ← fmt d
      let assignment := Layouts.assignmentDeclaration pat colonEqTk d
      let cond := combine #[.withSepAfter letTk space, assignment]
      return some { ifTk, cond, thenTk, thenBody, elseTk? := elseTk, elseBody? := elseBody }
  | _ =>
    pure none

@[builtin_conditional_fmt boolIfThenElse]
public def fmtBoolIfThenElse : ConditionalFmt := fun
  | `(boolIfThenElse| bif%$ifTk $c:term then%$thenTk $thenBody:term else%$elseTk $elseBody:term) =>
    do
      let cond ← fmt c
      return some { ifTk, cond, thenTk, thenBody, elseTk? := elseTk, elseBody? := elseBody }
  | _ =>
    pure none

@[builtin_fmt «term{_:_//_}»]
public def fmtSubtype : Fmt := fun
  | `(«term{_:_//_}»| {%$lbTk $x:ident $[ :%$colonTk? $type?:term]? //%$slashTk $p:term }%$rbTk) =>
    do
      let lbTk ← fmt lbTk
      let x ← fmt x
      let colonTk? ← fmt? colonTk?
      let type? ← fmt? type?
      let slashTk ← fmt slashTk
      let p ← fmt p
      let rbTk ← fmt rbTk
      let lhs := Layouts.typeAscription x colonTk? type?
      return Layouts.subtype lbTk lhs slashTk p rbTk .dense
  | _ =>
    throw .partialFormatter

@[builtin_fmt termWithout_expected_type_]
public def fmtWithoutExpectedType : Fmt := fun
  | `(term| without_expected_type%$tk $x:term) => do fmtAppLike #[tk, x]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.modCast]
public def fmtModCast : Fmt := fun
  | `(Lean.modCast| mod_cast%$tk $x:term) => do fmtAppLike #[tk, x]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.includeStr]
public def fmtIncludeStr : Fmt := fun
  | `(Lean.includeStr| include_str%$tk $x:term) => do fmtAppLike #[tk, x]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.withAnnotateTerm]
public def fmtWithAnnotateTerm : Fmt
  | `(withAnnotateTerm| with_annotate_term%$withAnnotateTermTk $stx:rawStx $t:term) => do
    fmtAppLike #[withAnnotateTermTk, stx, t]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.byElab]
public def fmtByElab : Fmt := fun
  | `(Lean.byElab| by_elab%$tk $doSeq:doSeq) => do
    let tk ← fmt tk
    let doSeq ← fmt doSeq
    return Layouts.keywordPrefixedSeq tk doSeq .nonSticky
  | _ =>
    throw .partialFormatter

/-! ## Attributes -/

@[builtin_fmt Lean.deprecated]
public def fmtDeprecated : Fmt := fun
  | `(Lean.deprecated| deprecated%$tk $[$id?:ident]? $[$msg?:str]?
      $[$typeChanged?:deprecatedTypeChanged]?
      $[ (%$lbTk? since%$sinceTk? :=%$colonEqTk? $since?:str )%$rbTk?]?) => do
    let tk ← fmt tk
    let id? ← fmt? id?
    let msg? ← fmt? msg?
    let typeChanged? ← fmt? typeChanged?
    let sinceParam? ← fmtNamedArgumentTerm? lbTk? sinceTk? colonEqTk? since? rbTk?
    return Layouts.pseudoApplication #[tk, id?, msg?, typeChanged?, sinceParam?]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.deprecated_arg]
public def fmtDeprecatedArg : Fmt := fun
  | `(Lean.deprecated_arg| deprecated_arg%$tk $old:ident $[$new?:ident]? $[$msg?:str]?
      $[(%$lbTk? since%$sinceTk? :=%$colonEqTk? $since?:str )%$rbTk?]?) => do
    let tk ← fmt tk
    let old ← fmt old
    let new? ← fmt? new?
    let msg? ← fmt? msg?
    let sinceParam? ← fmtNamedArgumentTerm? lbTk? sinceTk? colonEqTk? since? rbTk?
    return Layouts.pseudoApplication #[tk, old, new?, msg?, sinceParam?]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.suggest_for]
public def fmtSuggestFor : Fmt := fun
  | `(Lean.suggest_for| suggest_for%$tk $ids:ident*) => do
    let tk ← fmt tk
    let ids ← fmtArray ids
    return Layouts.pseudoApplication <| #[tk] ++ ids
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.univ_out_params]
public def fmtUnivOutParams : Fmt := fun
  | `(Lean.univ_out_params| univ_out_params%$tk $ids:ident*) => do
    let tk ← fmt tk
    let ids ← fmtArray ids
    return Layouts.pseudoApplication <| #[tk] ++ ids
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.command_code_action]
public def fmtCommandCodeAction : Fmt := fun
  | `(Lean.command_code_action| command_code_action%$tk $ids:ident*) => do
    let tk ← fmt tk
    let ids ← fmtArray ids
    return Layouts.pseudoApplication <| #[tk] ++ ids
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.builtin_command_code_action]
public def fmtBuiltinCommandCodeAction : Fmt := fun
  | `(Lean.builtin_command_code_action| builtin_command_code_action%$tk $ids:ident*) => do
    let tk ← fmt tk
    let ids ← fmtArray ids
    return Layouts.pseudoApplication <| #[tk] ++ ids
  | _ =>
    throw .partialFormatter

/-! ## Commands -/

public def fmtRunDoSeqCmd (tk : Syntax) (doSeq : Syntax) : FmtM TaggedDoc := do
  let tk ← fmt tk
  let doSeq ← fmt doSeq
  return Layouts.keywordPrefixedSeq tk doSeq .nonSticky

@[builtin_fmt Lean.runCmd]
public def fmtRunCmd : Fmt := fun
  | `(Lean.runCmd| run_cmd%$tk $doSeq:doSeq) => fmtRunDoSeqCmd tk doSeq
  | _ => throw .partialFormatter

@[builtin_fmt Lean.runElab]
public def fmtRunElab : Fmt := fun
  | `(Lean.runElab| run_elab%$tk $doSeq:doSeq) => fmtRunDoSeqCmd tk doSeq
  | _ => throw .partialFormatter

@[builtin_fmt Lean.runMeta]
public def fmtRunMeta : Fmt := fun
  | `(Lean.runMeta| run_meta%$tk $doSeq:doSeq) => fmtRunDoSeqCmd tk doSeq
  | _ => throw .partialFormatter

public def fmtReduceConfig (c : TSyntax ``reduceConfig) : FmtM (Array TaggedDoc) := do
  match c with
  | `(Lean.reduceConfig| $[(%$lbTks $ids:ident :=%$colonEqTks $ts:term )%$rbTks]*) =>
    let mut args : Array TaggedDoc := #[]
    for lbTk in lbTks, id in ids, colonEqTk in colonEqTks, t in ts, rbTk in rbTks do
      args := args.push <| ← fmtNamedArgumentTerm lbTk id colonEqTk t rbTk
    return args
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.reduceCmd]
public def fmtReduceCmd : Fmt := fun
  | `(Lean.reduceCmd| #reduce%$tk $config:reduceConfig $e:term) => do
    let tk ← fmt tk
    let config ← fmtReduceConfig config
    let «reduce» := Layouts.pseudoApplication <| #[tk] ++ config
    let e ← fmt e
    return Layouts.pseudoApplication #[«reduce», e]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.setLibrarySuggestionsCmd]
public def fmtSetLibrarySuggestions : Fmt := fun
  | `(Lean.setLibrarySuggestionsCmd| set_library_suggestions%$tk $t:term) => do
    let tk ← fmt tk
    let t ← fmt t
    return Layouts.pseudoApplication #[tk, t]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.discrTreeKeyCmd]
public def fmtDiscrTreeKeyCmd : Fmt := fun
  | `(Lean.Parser.discrTreeKeyCmd| #discr_tree_key%$tk $t:term) => do
    let tk ← fmt tk
    let t ← fmt t
    return Layouts.pseudoApplication #[tk, t]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.discrTreeSimpKeyCmd]
public def fmtDiscrTreeSimpKeyCmd : Fmt := fun
  | `(Lean.Parser.discrTreeSimpKeyCmd| #discr_tree_simp_key%$tk $t:term) => do
    let tk ← fmt tk
    let t ← fmt t
    return Layouts.pseudoApplication #[tk, t]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.commandSeal__]
public def fmtSeal : Fmt := fun
  | `(Lean.Parser.commandSeal__| seal%$tk $ids:ident*) => do
    let tk ← fmt tk
    let ids ← fmtArray ids
    return Layouts.pseudoApplication <| #[tk] ++ ids
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.commandUnseal__]
public def fmtUnseal : Fmt := fun
  | `(Lean.Parser.commandUnseal__| unseal%$tk $ids:ident*) => do
    let tk ← fmt tk
    let ids ← fmtArray ids
    return Layouts.pseudoApplication <| #[tk] ++ ids
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.timeCmd]
public def fmtTimeCmd : Fmt := fun
  | `(Lean.Parser.timeCmd| #time%$tk $cmd:command) => do
    let tk ← fmt tk
    let cmd ← fmt cmd
    return Layouts.spacedAtomic #[tk, cmd]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.checkTactic]
public def fmtCheckTactic : Fmt := fun
  | `(Lean.Parser.checkTactic|
      #check_tactic%$tk $lhs:term ~>%$arrowTk $rhs:term by%$byTk $tac:tactic) => do
    let tk ← fmt tk
    let lhs ← fmt lhs
    let arrowTk ← fmt arrowTk
    let rhs ← fmt rhs
    let byTk ← fmt byTk
    let tac ← fmt tac
    let rel := Layouts.infixOperator #[lhs, arrowTk, rhs]
    let head := Layouts.pseudoApplication #[tk, rel]
    return Layouts.keywordSeparated head byTk tac
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.checkTacticFailure]
public def fmtCheckTacticFailure : Fmt := fun
  | `(Lean.Parser.checkTacticFailure| #check_tactic_failure%$tk $t:term by%$byTk $tac:tactic) => do
    let tk ← fmt tk
    let t ← fmt t
    let head := Layouts.pseudoApplication #[tk, t]
    let byTk ← fmt byTk
    let tac ← fmt tac
    return Layouts.keywordSeparated head byTk tac
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.checkSimp]
public def fmtCheckSimp : Fmt := fun
  | `(Lean.Parser.checkSimp| #check_simp%$tk $lhs:term ~>%$arrowTk $rhs:term) => do
    let tk ← fmt tk
    let lhs ← fmt lhs
    let arrowTk ← fmt arrowTk
    let rhs ← fmt rhs
    let rel := Layouts.infixOperator #[lhs, arrowTk, rhs]
    return Layouts.pseudoApplication #[tk, rel]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.checkSimpFailure]
public def fmtCheckSimpFailure : Fmt := fun
  | `(Lean.Parser.checkSimpFailure| #check_simp%$tk $t:term !~>%$failTk) => do
    let tk ← fmt tk
    let t ← fmt t
    let failTk ← fmt failTk
    let post := Layouts.postfixOperator t failTk .withSpacing
    return Layouts.pseudoApplication #[tk, post]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.guardMsgsFilter]
public def fmtGuardMsgsFilter : Fmt := fun
  | `(Lean.guardMsgsFilter| $[$action?:guardMsgsFilterAction]? $severity:guardMsgsFilterSeverity) =>
    do
      let action? ← fmt? action?
      let severity ← fmt severity
      return Layouts.pseudoApplication #[action?, severity]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.guardMsgsWhitespace]
public def fmtGuardMsgsWhitespace : Fmt := fun
  | `(Lean.guardMsgsWhitespace| whitespace%$tk :=%$colonEqTk $arg:guardMsgsWhitespaceArg) => do
    let tk ← fmt tk
    let colonEqTk ← fmt colonEqTk
    let arg ← fmt arg
    return Layouts.assignmentDeclaration tk colonEqTk arg
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.guardMsgsOrdering]
public def fmtGuardMsgsOrdering : Fmt := fun
  | `(Lean.guardMsgsOrdering| ordering%$tk :=%$colonEqTk $arg:guardMsgsOrderingArg) => do
    let tk ← fmt tk
    let colonEqTk ← fmt colonEqTk
    let arg ← fmt arg
    return Layouts.assignmentDeclaration tk colonEqTk arg
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.guardMsgsPositions]
public def fmtGuardMsgsPositions : Fmt := fun
  | `(Lean.guardMsgsPositions| positions%$tk :=%$colonEqTk $arg:guardMsgsPositionsArg) => do
    let tk ← fmt tk
    let colonEqTk ← fmt colonEqTk
    let arg ← fmt arg
    return Layouts.assignmentDeclaration tk colonEqTk arg
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.guardMsgsSubstring]
public def fmtGuardMsgsSubstring : Fmt
  | `(Lean.guardMsgsSubstring| substring%$tk :=%$colonEqTk $rhs) => do
    let tk ← fmt tk
    let colonEqTk ← fmt colonEqTk
    let arg ← fmt rhs
    return Layouts.assignmentDeclaration tk colonEqTk arg
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.guardMsgsSpecElt]
public def fmtGuardMsgsSpecElt : Fmt := fun stx => do fmt (← getStxArg! stx 0)

@[builtin_fmt Lean.guardMsgsSpec]
public def fmtGuardMsgsSpec : Fmt := fun
  | `(Lean.guardMsgsSpec| (%$lbTk $elts:guardMsgsSpecElt,* )%$rbTk) => do
    let lbTk ← fmt lbTk
    let elts ← fmtTSepArray elts
    let rbTk ← fmt rbTk
    return Layouts.collection lbTk elts rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.guardMsgsCmd]
public def fmtGuardMsgsCmd : Fmt := fun
  | `(Lean.guardMsgsCmd|
      $[$doc?:docComment]?
      #guard_msgs%$tk $[$spec?:guardMsgsSpec]? in%$inTk
      $cmd:command) => do
    let doc? ← fmt? doc?
    let tk ← fmt tk
    let spec? ← fmt? spec?
    let head := Layouts.pseudoApplication #[tk, spec?]
    let inTk ← fmt inTk
    let cmd ← fmt cmd
    let body :=
      Layouts.keywordSeparated head inTk cmd { allowFlattening := false, nestedRhs := false }
    return Layouts.lines #[doc?, body]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.guardPanicCmd]
public def fmtGuardPanicCmd : Fmt := fun
  | `(Lean.guardPanicCmd| #guard_panic%$tk in%$inTk $cmd:command) => do
    let tk ← fmt tk
    let inTk ← fmt inTk
    let cmd ← fmt cmd
    return Layouts.lines #[Layouts.spacedAtomic #[tk, inTk], cmd]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.infoTreesCmd]
public def fmtInfoTreesCmd : Fmt := fun
  | `(Lean.infoTreesCmd| #info_trees%$tk in%$inTk $cmd:command) => do
    let tk ← fmt tk
    let inTk ← fmt inTk
    let cmd ← fmt cmd
    return Layouts.lines #[Layouts.spacedAtomic #[tk, inTk], cmd]
  | _ =>
    throw .partialFormatter
