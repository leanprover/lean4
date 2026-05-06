/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
public import Lean.Fmt.Formatters.Lean.Parser.Term
meta import Init.NotationExtra
meta import Init.Notation
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data
import Init.While
import Lean.Fmt.Util.Basic

namespace Lean.Fmt

@[builtin_fmt Lean.«term_Matches_|»]
public def fmtTermMatches : Fmt := fun
  | `($lhs:term matches%$matchesTk $pats:term|*) => do
    let lhs ← fmt lhs
    let matchesTk ← fmt matchesTk
    let pats ← fmtTSepArray pats
    if h : pats.elemsAndSeps.size = 1 then
      return Layouts.keywordSeparated lhs matchesTk pats.elemsAndSeps[0]
    let primaryPat := nested <| pats.elemsAndSeps[0]!
    let secondaryPats := fmtSecondaryPats <| pats.elemsAndSeps[1...*].toArray
    let matchesBlock :=
      maybeFlattened <| oneOf #[
        combine #[
          .withSepAfter matchesTk space,
          .withSepAfter (flattened primaryPat) ⟨nl, nested⟩,
          secondaryPats
        ],
        combine #[
          .withSepAfter matchesTk ⟨nl, nested⟩,
          .withSepAfter primaryPat nl,
          secondaryPats
        ]
      ]
    return Layouts.spacedAtomic #[hardNested lhs, matchesBlock]
  | _ =>
    throw .partialFormatter
where
  fmtSecondaryPats (secondaryPats : Array TaggedDoc) : TaggedDoc := Id.run do
    let mut i := 0
    let mut lines := #[]
    while i < secondaryPats.size do
      let sep := secondaryPats[i]!
      let pat := secondaryPats[i + 1]!
      lines := lines.push <| nested <| Layouts.softSpacedAtomic #[sep, pat]
      i := i + 2
    let lineComponents := lines.map (.withSepAfter · nl)
    return combine lineComponents

/-! ## Explicit binders -/

@[builtin_fmt Lean.unbracketedExplicitBinders]
public def fmtUnbracketedExplicitBinders : Fmt := fun
  | `(Lean.unbracketedExplicitBinders| $ids* $[ :%$typeAscriptionTk? $type?:term]?) =>
    fmtBinder #[] ids #[] typeAscriptionTk? type? none #[]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.bracketedExplicitBinders]
public def fmtBracketedExplicitBinders : Fmt := fun
  | `(Lean.bracketedExplicitBinders| (%$lbTk $ids* :%$typeAscriptionTk $type:term )%$rbTk) =>
    fmtBinder #[lbTk] ids #[] (some typeAscriptionTk) (some type) none #[rbTk]
  | _ =>
    throw .partialFormatter

public def explicitBindersToGroup (bs : TSyntax ``Lean.explicitBinders) : Array Syntax :=
  match bs with
  | `(Lean.explicitBinders| $b:unbracketedExplicitBinders) => #[b]
  | `(Lean.explicitBinders| $[$bs:bracketedExplicitBinders]*) => bs
  | _ => #[]

@[builtin_quantifier_fmt «term∃_,_»]
public def fmtExists : QuantifierFmt := fun
  | `(∃%$exTk $bs:explicitBinders ,%$commaTk $body:term) =>
    some {
      quantifier := exTk
      binders := .binders #[#[explicitBindersToGroup bs]]
      typeAscriptionTk? := none
      type? := none
      commaTk
      body
    }
  | _ =>
    none

@[builtin_quantifier_fmt «termExists_,_»]
public def fmtExistsKeyword : QuantifierFmt := fun
  | `(exists%$existsTk $bs:explicitBinders ,%$commaTk $body:term) =>
    some {
      quantifier := existsTk
      binders := .binders #[#[explicitBindersToGroup bs]]
      typeAscriptionTk? := none
      type? := none
      commaTk
      body
    }
  | _ =>
    none

@[builtin_quantifier_fmt «termΣ_,_»]
public def fmtSigma : QuantifierFmt := fun
  | `(Σ%$sigmaTk $bs:explicitBinders ,%$commaTk $body:term) =>
    some {
      quantifier := sigmaTk
      binders := .binders #[#[explicitBindersToGroup bs]]
      typeAscriptionTk? := none
      type? := none
      commaTk
      body
    }
  | _ =>
    none

@[builtin_quantifier_fmt «termΣ'_,_»]
public def fmtPSigma : QuantifierFmt := fun
  | `(Σ'%$psigmaTk $bs:explicitBinders ,%$commaTk $body:term) =>
    some {
      quantifier := psigmaTk
      binders := .binders #[#[explicitBindersToGroup bs]]
      typeAscriptionTk? := none
      type? := none
      commaTk
      body
    }
  | _ =>
    none

@[builtin_infix_fmt «term_×_»]
public def fmtTimes : Fmt.InfixOperation := {
  sparse := false
  precs? := some { prec := 35, lhsPrec := 36, rhsPrec := 35 }
  extendedChainKinds := {``«term_×__1»}
}

@[builtin_infix_fmt «term_×__1»]
public def fmtSigmaTimes : Fmt.InfixOperation := {
  sparse := false
  precs? := some { prec := 35, lhsPrec := 0, rhsPrec := 35 }
  extendedChainKinds := {``«term_×_»}
}

@[builtin_infix_fmt «term_×'_»]
public def fmtTimes' : Fmt.InfixOperation := {
  sparse := false
  precs? := some { prec := 35, lhsPrec := 36, rhsPrec := 35 }
  extendedChainKinds := {``«term_×'__1»}
}

@[builtin_infix_fmt «term_×'__1»]
public def fmtPSigmaTimes : Fmt.InfixOperation := {
  sparse := false
  precs? := some { prec := 35, lhsPrec := 0, rhsPrec := 35 }
  extendedChainKinds := {``«term_×'_»}
}

@[builtin_fmt «term{_}»]
public def fmtSetNotation : Fmt := fun
  | `({%$lbTk $elems:term,* }%$rbTk) => do fmtSetNotationLike lbTk elems rbTk
  | _ => throw .partialFormatter

@[builtin_infix_fmt Lean.unifConstraint]
public def fmtUnifConstraint : Fmt.InfixOperation := {
  sparse := true
  precs? := some { prec := 0, lhsPrec := 0, rhsPrec := 0 }
}

@[builtin_fmt Lean.«command__Unif_hint____Where_|_-⊢__»]
public def fmtUnifHint : Fmt := fun
  | stx@`(command|
      $[$docComment?:docComment]?
      $attrKind:attrKind unif_hint%$unifHintTk $[$declId?:ident]? $binders* where%$whereTk
        $[$constraints:unifConstraint $[,%$commaTks]?]* ⊢ $rhs:unifConstraint) => do
    let docComment? ← fmt? docComment?
    let signature ← fmtDeclarationSignature #[attrKind, unifHintTk] none declId? binders none none
    let whereTk ← fmt whereTk
    let constraints := Syntax.TSepArray.ofElemsAndSeps constraints commaTks ","
    let constraints ← fmtTSepArray constraints
    let vdash ← fmtAtomic stx[7]
    let rhs ← fmt rhs
    let constraints := Layouts.sepLines constraints (includeSeps := false)
    let body := Layouts.horizontalOrVertical #[constraints, vdash, rhs]
    let mainDecl := Layouts.whereDeclaration signature whereTk body
    return Layouts.lines #[docComment?, mainDecl]
  | _ =>
    throw .partialFormatter

/-! ## `class abbrev` -/

@[builtin_fmt Lean.Parser.Command.classAbbrev]
public def fmtClassAbbrev : Fmt := fun
  | `(Parser.Command.classAbbrev|
      $mods:declModifiers class%$classTk abbrev%$abbrevTk $declId:declId $binders*
        $[:%$typeAscriptionTk? $type?:term]? :=%$colonEqTk $[ $parents:term $[,%$commaTks]? ]*) =>
    do
      let signature ←
        fmtDeclarationSignature #[classTk, abbrevTk] none declId binders typeAscriptionTk? type?
      let colonEqTk ← fmt colonEqTk
      let parents := Syntax.TSepArray.ofElemsAndSeps parents commaTks ","
      let parents ← fmtTSepArray parents
      let parents := Layouts.sepFill parents
      let decl := Layouts.assignmentDeclaration signature colonEqTk parents
      fmtDeclWithDeclModifiers mods decl
  | _ =>
    throw .partialFormatter

@[builtin_fmt «tacticFunext___»]
public def fmtFunext : Fmt := fun
  | `(tactic| funext%$funextTk $args:term*) => do
    let funextTk ← fmt funextTk
    let args ← fmtArray args
    return Layouts.pseudoApplication (format := { parenthesize := true }) <| #[funextTk] ++ args
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.cdot]
public def fmtCdotTactic : Fmt := fun
  -- `·` also matches the ASCII `.` spelling.
  | `(tactic| ·%$cdotTk $tacticSeq:tacticSeq) => do
    let cdotTk ← fmt cdotTk
    -- `tacticSeqIndentGt` formats with its own `withPosition`, so the first tactic stays on the `·`
    -- line and subsequent tactics align below it.
    let tacticSeq ← fmt tacticSeq
    return pseudoAligned <| nested <| Layouts.softSpacedAtomic #[cdotTk, tacticSeq]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.solveTactic]
public def fmtSolve : Fmt := fun
  | `(tactic| solve%$solveTk $[|%$barTks $tacticSeqs:tacticSeq]*) => do
    fmtAltsTactic solveTk barTks tacticSeqs
  | _ =>
    throw .partialFormatter

public def fmtCalcStepLike (pred : Syntax) (colonEqTk? proof? : Option Syntax)
    : FmtM TaggedDoc := do
  let colonEqTk? ← fmt? colonEqTk?
  let proof? ← fmt? proof?
  if colonEqTk?.isAlwaysEmpty || proof?.isAlwaysEmpty then
    return ← fmt pred
  if pred.getArgs.size != 3 then
    let pred ← fmt pred
    return Layouts.assignmentDeclaration pred colonEqTk? proof?
  let lhs := pred[0]!
  let op := pred[1]!
  let rhs := pred[2]!
  let lhs ← fmt lhs
  let op ← fmt op
  let rhs ← fmt rhs
  let shortProofPred :=
    Layouts.infixOperator #[lhs, op, flattened rhs] <| .sparse (alignedOperators := true)
  let shortProofVariant :=
    combine #[
      .withSepAfter shortProofPred space,
      .withSepAfter colonEqTk? space,
      flattened proof?
    ]
  let longProofPred := Layouts.infixOperator #[lhs, op, rhs] .sparse
  let longProofVariant := Layouts.assignmentDeclaration longProofPred colonEqTk? proof?
  return fallbackOnOverflow shortProofVariant longProofVariant

@[builtin_fmt Lean.calcFirstStep]
public def fmtCalcFirstStep : Fmt := fun
  | `(Lean.calcFirstStep| $pred:term $[ :=%$colonEqTk? $proof?:term]?) => do
    fmtCalcStepLike pred colonEqTk? proof?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.calcStep]
public def fmtCalcStep : Fmt := fun
  | `(Lean.calcStep| $pred:term :=%$colonEqTk $proof:term) => do
    fmtCalcStepLike pred colonEqTk proof
  | _ =>
    throw .partialFormatter

public def fmtCalcSteps (calcSteps : Syntax) : FmtM (Array TaggedDoc) := do
  let firstStep ← fmt (← getStxArg! calcSteps 0)
  let otherSteps ← (← getStxArg! calcSteps 1).getArgs.mapM fmt
  return #[firstStep] ++ otherSteps

public def fmtCalc (calcTk : Syntax) (calcSteps : TSyntax ``calcSteps) : FmtM TaggedDoc := do
  let calcTk ← fmt calcTk
  let calcSteps ← fmtCalcSteps calcSteps
  return Layouts.keywordPrefixedSeq calcTk (withPosition <| Layouts.lines calcSteps) .nonSticky

@[builtin_fmt Lean.«calc»]
public def fmtCalcTerm : Fmt := fun
  | `(term| calc%$calcTk $steps:calcSteps) => fmtCalc calcTk steps
  | _ => throw .partialFormatter

@[builtin_fmt Lean.calcTactic]
public def fmtCalcTactic : Fmt := fun
  | `(tactic| calc%$calcTk $steps:calcSteps) => fmtCalc calcTk steps
  | _ => throw .partialFormatter

@[builtin_fmt Lean.convCalc_]
public def fmtConvCalc : Fmt := fun
  | `(conv| calc%$calcTk $steps:calcSteps) => fmtCalc calcTk steps
  | _ => throw .partialFormatter
