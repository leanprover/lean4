/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
import Lean.Fmt.Formatters.Lean.Parser.Term.Basic
import Lean.Fmt.Formatters.Lean.Parser.Term
public import Lean.Fmt.FmtM.Basic
meta import Lean.Parser.Do
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Parser.Term.nestedAction]
public def fmtNestedAction : Fmt := fun
  | `(Parser.Term.nestedAction| ←%$leftArrowTk $elem:doElem) => do
    let leftArrowTk ← fmt leftArrowTk
    let elem ← fmt elem
    return Layouts.prefixOperator leftArrowTk elem .withSpacing
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.doExpr]
public def fmtDoExpr : Fmt := fun
  | `(Parser.Term.doExpr| $t:term) => fmt t
  | _ => throw .partialFormatter

public def fmtDoSeqItems (items : TSyntaxArray ``Parser.Term.doSeqItem) : FmtM TaggedDoc := do
  let seq : Syntax.TSepArray `doElem ";" :=
    ⟨← items.flatMapM fun
      | `(Parser.Term.doSeqItem| $elem:doElem $[;%$semicolonTk?]?) => do
        let semicolonTk := semicolonTk?.getD (mkNullNode #[])
        return #[elem.raw, semicolonTk]
      | _ =>
        throw .partialFormatter⟩
  fmtSeq seq ``Parser.Term.doNested

@[builtin_fmt Lean.Parser.Term.doSeqIndent]
public def fmtDoSeqIndent : Fmt := fun
  | `(Parser.Term.doSeqIndent| $items:doSeqItem*) => do fmtDoSeqItems items
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.doSeqBracketed]
public def fmtDoSeqBracketed : Fmt := fun
  | `(Parser.Term.doSeqBracketed|
      {%$lbTk
        $items:doSeqItem*
      }%$rbTk ) => do
    let lbTk ← fmt lbTk
    let items ← fmtDoSeqItems items
    let rbTk ← fmt rbTk
    return Layouts.bracketed lbTk items rbTk <| .sparse hardNl
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.do]
public def fmtDo : Fmt := fun
  | `(Parser.Term.do| do%$doTk $doSeq:doSeq) => do
    let doTk ← fmt doTk
    let doSeq ← fmt doSeq
    return Layouts.keywordPrefixedSeq doTk doSeq .sticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.termReturn]
public def fmtTermReturn : Fmt := fun
  | `(Parser.Term.termReturn| return%$returnTk $[$t?:term]?) => do
    let returnTk ← fmt returnTk
    let t? ← fmt? t?
    return withPosition <| Layouts.prefixOperator returnTk t? .withSpacing
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.doBreak]
public def fmtDoBreak : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Term.doContinue]
public def fmtDoContinue : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Term.doReturn]
public def fmtDoReturn : Fmt := fun
  | `(Parser.Term.doReturn| return%$returnTk $[$e?:term]?) => do
    let returnTk ← fmt returnTk
    let e? ← fmt? e?
    return withPosition <| Layouts.prefixOperator returnTk e? .withSpacing
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.doDbgTrace]
public def fmtDoDbgTrace : Fmt := fun
  | `(Parser.Term.doDbgTrace| dbg_trace%$dbgTraceTk $e) => do
    let dbgTraceTk ← fmt dbgTraceTk
    let e ← fmt e
    return Layouts.pseudoApplication #[dbgTraceTk, e]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.doIdbg]
public def fmtDoIdbg : Fmt := fun
  | `(Parser.Term.doIdbg| idbg%$idbgTk $e:term) => do
    let idbgTk ← fmt idbgTk
    let e ← fmt e
    return Layouts.pseudoApplication #[idbgTk, e]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.doAssert]
public def fmtDoAssert : Fmt := fun
  | `(Parser.Term.doAssert| assert!%$assertTk $e:term) => do
    let assertTk ← fmt assertTk
    let e ← fmt e
    return Layouts.pseudoApplication #[assertTk, e]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.doDebugAssert]
public def fmtDoDebugAssert : Fmt := fun
  | `(Parser.Term.doDebugAssert| debug_assert!%$debugAssertTk $e:term) => do
    let debugAssertTk ← fmt debugAssertTk
    let e ← fmt e
    return Layouts.pseudoApplication #[debugAssertTk, e]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.doRepeat]
public def fmtDoRepeat : Fmt := fun
  | `(Parser.Term.doRepeat| repeat%$repeatTk $seq:doSeq) => do
    let repeatTk ← fmt repeatTk
    let seq ← fmt seq
    return Layouts.keywordPrefixedSeq repeatTk seq .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.doLet]
public def fmtDoLet : Fmt := fun
  | `(Parser.Term.doLet| let%$letTk $[mut%$mutTk?]? $cfg:letConfig $decl:letDecl) => do
    let letTk ← fmt letTk
    let mutTk? ← fmt? mutTk?
    let cfg ← fmt cfg
    let decl ← fmt decl
    let kw := Layouts.spacedAtomic #[letTk, mutTk?]
    return Layouts.letDecl kw cfg decl
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.doHave]
public def fmtDoHave : Fmt := fun
  | `(Parser.Term.doHave| have%$haveTk $cfg:letConfig $decl:letDecl) => do
    let haveTk ← fmt haveTk
    let cfg ← fmt cfg
    let decl ← fmt decl
    return Layouts.letDecl haveTk cfg decl
  | _ =>
    throw .partialFormatter

public def fmtDoLetElseLike
    (decl : TaggedDoc) (declComponents : Array Syntax) (pipeTk? : Option Syntax)
    (elseSeq? : Option Syntax) (body? : Option Syntax)
    : FmtM TaggedDoc := do
  let instructionComponents := declComponents ++ pipeTk?.toArray ++ elseSeq?.toArray
  let pipeTk? ← fmt? pipeTk?
  let elseSeq? ← fmt? elseSeq?
  let elseClause? := nested <| Layouts.softSpacedAtomic #[pipeTk?, elseSeq?]
  let instruction :=
    if !elseClause?.isAlwaysEmpty then
      Layouts.matchDeclaration decl elseClause?
    else
      decl
  let some body := body?
    | return withPosition instruction
  fmtTermInstruction instruction instructionComponents none body

public def fmtWithDoIdDecl
    (kws : Array Syntax) (cfg? : Option (TSyntax ``Parser.Term.letConfig))
    (idDecl : TSyntax ``Parser.Term.doIdDecl)
    : FmtM TaggedDoc := do
  let `(Parser.Term.doIdDecl| $id:ident $[:%$typeAscriptionTk? $type?:term]? ←%$leftArrowTk $elem:doElem) :=
      idDecl
    | throw .partialFormatter
  let kws ← kws.mapM fmt
  let cfg? ← fmt? cfg?
  let id ← fmt id
  let typeAscriptionTk? ← fmt? typeAscriptionTk?
  let type? ← fmt? type?
  let leftArrowTk ← fmt leftArrowTk
  let elem ← fmt elem
  let kws := Layouts.spacedAtomic kws
  let signature := Layouts.localSignature #[id] #[] typeAscriptionTk? type?
  let decl := Layouts.assignmentDeclaration signature leftArrowTk elem
  return Layouts.letDecl kws cfg? decl

public def fmtWithDoPatDecl
    (kws : Array Syntax) (cfg? : Option (TSyntax ``Parser.Term.letConfig))
    (patDecl : TSyntax ``Parser.Term.doPatDecl)
    : FmtM TaggedDoc := do
  let `(Parser.Term.doPatDecl|
      $pat:term $[:%$typeAscriptionTk? $type?:term]? ←%$leftArrowTk $elem:doElem
        $[|%$pipeTk? $elseSeq?:doSeqIndent $[$body?:doSeqIndent]?]?) :=
      patDecl
    | throw .partialFormatter
  let declComponents :=
    kws ++ cfg?.toArray ++ #[pat] ++ typeAscriptionTk?.toArray ++ type?.toArray
      ++ #[leftArrowTk, elem]
  let kws ← kws.mapM fmt
  let cfg? ← fmt? cfg?
  let signature ← fmtPatSignature pat typeAscriptionTk? type?
  let leftArrowTk ← fmt leftArrowTk
  let elemDoc ← fmt elem
  let kws := Layouts.spacedAtomic kws
  let decl := Layouts.assignmentDeclaration signature leftArrowTk elemDoc
  let fullDecl := Layouts.letDecl kws cfg? decl
  fmtDoLetElseLike fullDecl declComponents pipeTk? elseSeq? body?.join

@[builtin_fmt Lean.Parser.Term.doLetArrow]
public def fmtDoLetArrow : Fmt := fun
  | `(Parser.Term.doLetArrow| let%$letTk $[mut%$mutTk?]? $cfg:letConfig $decl:doIdDecl) => do
    fmtWithDoIdDecl (#[letTk] ++ mutTk?.toArray) cfg decl
  | `(Parser.Term.doLetArrow| let%$letTk $[mut%$mutTk?]? $cfg:letConfig $decl:doPatDecl) => do
    fmtWithDoPatDecl (#[letTk] ++ mutTk?.toArray) cfg decl
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.doLetElse]
public def fmtDoLetElse : Fmt := fun
  | `(Parser.Term.doLetElse|
      let%$letTk $[mut%$mutTk?]? $cfg:letConfig $pat:term :=%$colonEqTk $value:term
        |%$pipeTk $elseSeq:doSeqIndent $[$body?:doSeqIndent]?) => do
    let declComponents := #[letTk] ++ mutTk?.toArray ++ #[cfg.raw, pat.raw, colonEqTk, value.raw]
    let letTk ← fmt letTk
    let mutTk? ← fmt? mutTk?
    let cfg ← fmt cfg
    let pat ← fmt pat
    let colonEqTk ← fmt colonEqTk
    let value ← fmt value
    let kw := Layouts.spacedAtomic #[letTk, mutTk?]
    let assignment := Layouts.assignmentDeclaration pat colonEqTk value
    let decl := Layouts.letDecl kw cfg assignment
    fmtDoLetElseLike decl declComponents pipeTk elseSeq.raw (body?.map (·.raw))
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.doLetExpr]
public def fmtDoLetExpr : Fmt := fun
  | `(Parser.Term.doLetExpr|
      let_expr%$letExprTk $pat:matchExprPat :=%$colonEqTk $value:term
        |%$pipeTk $elseSeq:doSeqIndent $[$body?:doSeqIndent]?) => do
    let declComponents := #[letExprTk, pat.raw, colonEqTk, value.raw]
    let letExprTk ← fmt letExprTk
    let pat ← fmt pat
    let colonEqTk ← fmt colonEqTk
    let value ← fmt value
    let assignment := Layouts.assignmentDeclaration pat colonEqTk value
    let decl := Layouts.letDecl letExprTk empty assignment
    fmtDoLetElseLike decl declComponents pipeTk elseSeq.raw (body?.map (·.raw))
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.doLetMetaExpr]
public def fmtDoLetMetaExpr : Fmt := fun
  | `(Parser.Term.doLetMetaExpr|
      let_expr%$letExprTk $pat:matchExprPat ←%$leftArrowTk $value:term
        |%$pipeTk $elseSeq:doSeqIndent $[$body?:doSeqIndent]?) => do
    let declComponents := #[letExprTk, pat.raw, leftArrowTk, value.raw]
    let letExprTk ← fmt letExprTk
    let pat ← fmt pat
    let leftArrowTk ← fmt leftArrowTk
    let value ← fmt value
    let assignment := Layouts.assignmentDeclaration pat leftArrowTk value
    let decl := Layouts.letDecl letExprTk empty assignment
    fmtDoLetElseLike decl declComponents pipeTk elseSeq.raw (body?.map (·.raw))
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.doLetRec]
public def fmtDoLetRec : Fmt := fun
  | `(Parser.Term.doLetRec| let%$letTk rec%$recTk $decls:letRecDecls) =>
    fmtFullLetRecDecl #[letTk, recTk] decls
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.letIdDeclNoBinders]
public def fmtLetIdDeclNoBinders : Fmt := fun
  | `(Parser.Term.letIdDeclNoBinders| $letId:ident $[:%$typeAscriptionTk? $type?:term]? :=%$colonEqTk $body:term) =>
    do
      let letId ← fmt letId
      let typeAscriptionTk? ← fmt? typeAscriptionTk?
      let type? ← fmt? type?
      let colonEqTk ← fmt colonEqTk
      let body ← fmt body
      let signature := Layouts.localSignature #[letId] #[] typeAscriptionTk? type?
      return Layouts.assignmentDeclaration signature colonEqTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.doReassign]
public def fmtDoReassign : Fmt := fun
  | `(Parser.Term.doReassign| $decl:letIdDeclNoBinders) => fmt decl
  | `(Parser.Term.doReassign| $decl:letPatDecl) => fmt decl
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.doReassignArrow]
public def fmtDoReassignArrow : Fmt := fun
  | `(Parser.Term.doReassignArrow| $decl:doIdDecl) => fmtWithDoIdDecl #[] none decl
  | `(Parser.Term.doReassignArrow| $decl:doPatDecl) => fmtWithDoPatDecl #[] none decl
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.doIfProp]
public def fmtDoIfProp : Fmt := fun
  | `(Parser.Term.doIfProp| $[$h? :%$colonTk?]? $c:term) => do
    let h? ← fmt? h?
    let colonTk? ← fmt? colonTk?
    let c ← fmt c
    return Layouts.typeAscription h? colonTk? c
  | _ =>
    throw .partialFormatter

public def fmtDoIfLetLike (letTk pat sepTk value : Syntax) : FmtM TaggedDoc := do
  let letTk ← fmt letTk
  let pat ← fmt pat
  let sepTk ← fmt sepTk
  let value ← fmt value
  let assignment := Layouts.assignmentDeclaration pat sepTk value
  return Layouts.letDecl letTk empty assignment

@[builtin_fmt Lean.Parser.Term.doIfLet]
public def fmtDoIfLet : Fmt := fun
  | `(Parser.Term.doIfLet| let%$letTk $pat:term :=%$colonEqTk $value:term) =>
    fmtDoIfLetLike letTk pat colonEqTk value
  | `(Parser.Term.doIfLet| let%$letTk $pat:term ←%$leftArrowTk $value:term) =>
    fmtDoIfLetLike letTk pat leftArrowTk value
  | _ =>
    throw .partialFormatter

@[builtin_conditional_fmt Lean.Parser.Term.doIf]
public def fmtDoIf : ConditionalFmt := fun
  | `(Parser.Term.doIf|
      if%$ifTk $cond:doIfCond then%$thenTk $thenBlock:doSeq
        $[else%$elseIfElseTks if%$elseIfIfTks $elseIfConds:doIfCond then%$elseIfThenTks
          $elseIfBlocks:doSeq]*
        $[else%$elseTk? $elseBody?:doSeq]?) => do
    let cond ← fmt cond
    let mut elseIfs : Array Conditional.ElseIf := #[]
    for elseTk in elseIfElseTks, ifTk in elseIfIfTks, cond in elseIfConds, thenTk in elseIfThenTks,
      thenBlock in elseIfBlocks
    do
      let cond ← fmt cond
      elseIfs := elseIfs.push { elseTk, ifTk, cond, thenTk, body := thenBlock }
    return some { ifTk, cond, thenTk, thenBody := thenBlock, elseIfs, elseTk?, elseBody? }
  | _ =>
    pure none

public def fmtUnlessLike (unlessTk cond doTk seq : Syntax) : FmtM TaggedDoc := do
  let unlessTk ← fmt unlessTk
  let cond ← fmt cond
  let lhs := Layouts.pseudoApplication #[unlessTk, cond]
  let doTk ← fmt doTk
  let seq ← fmt seq
  return Layouts.keywordSeparated lhs doTk seq { allowFlattening := false }

@[builtin_fmt Lean.Parser.Term.doUnless]
public def fmtDoUnless : Fmt := fun
  | `(Parser.Term.doUnless| unless%$unlessTk $cond:term do%$doTk $seq:doSeq) =>
    fmtUnlessLike unlessTk cond doTk seq
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.termUnless]
public def fmtTermUnless : Fmt := fun
  | `(Parser.Term.termUnless| unless%$unlessTk $cond:term do%$doTk $seq:doSeq) =>
    fmtUnlessLike unlessTk cond doTk seq
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.doForDecl]
public def fmtDoForDecl : Fmt := fun
  | `(Parser.Term.doForDecl| $[$id?:ident :%$colonTk?]? $pat:term in%$inTk $collection:term) => do
    let id? ← fmt? id?
    let colonTk? ← fmt? colonTk?
    let pat ← fmt pat
    let inTk ← fmt inTk
    let collection ← fmt collection
    let lhs := Layouts.typeAscription id? colonTk? pat
    return Layouts.keywordSeparated lhs inTk collection
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.doFor]
public def fmtDoFor : Fmt := fun
  | `(Parser.Term.doFor| for%$forTk $decls:doForDecl,* do%$doTk $seq:doSeq) => do
    let forTk ← fmt forTk
    let decls ← fmtTSepArray decls
    let doTk ← fmt doTk
    let seq ← fmt seq
    let lhs := Layouts.keywordPrefixedSepFill forTk decls .nonSticky
    return Layouts.keywordSeparated lhs doTk seq { allowFlattening := false }
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.termFor]
public def fmtTermFor : Fmt := fun
  | `(Parser.Term.termFor| for%$forTk $decls:doForDecl,* do%$doTk $seq:doSeq) => do
    let forTk ← fmt forTk
    let decls ← fmtTSepArray decls
    let doTk ← fmt doTk
    let seq ← fmt seq
    let lhs := Layouts.keywordPrefixedSepFill forTk decls .nonSticky
    return Layouts.keywordSeparated lhs doTk seq { allowFlattening := false }
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.dependentParam]
public def fmtDependentParam : Fmt := fun
  | `(Parser.Term.dependentParam| (%$lbTk dependent%$dependentTk :=%$colonEqTk $val )%$rbTk) =>
    fmtNamedArgumentTerm lbTk dependentTk colonEqTk val rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.doMatch]
public def fmtDoMatch : Fmt := fun
  | `(Parser.Term.doMatch|
      match%$matchTk $[$dependentParam?:dependentParam]? $[$generalizingParam?:generalizingParam]? $[$motive?:motive]? $discrs:matchDiscr,* with%$withTk
      $alts:matchAlts) => do
    let matchTk ← fmt matchTk
    let dependentParam? ← fmt? dependentParam?
    let generalizingParam? ← fmt? generalizingParam?
    let motive? ← fmt? motive?
    let matchLhs :=
      Layouts.pseudoApplication #[matchTk, dependentParam?, generalizingParam?, motive?]
    let discrs ← fmtTSepArray discrs
    let withTk ← fmt withTk
    let alts ← fmt alts
    let «match» := Layouts.keywordPrefixedSepFill matchLhs discrs .nonSticky
    return Layouts.keywordSeparated «match» withTk alts {
      allowFlattening := false
      nestedRhs := false
    }
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.doMatchExpr]
public def fmtDoMatchExpr : Fmt := fun
  | `(Parser.Term.doMatchExpr|
      match_expr%$matchExprTk $[(%$lbTk? meta%$metaTk? :=%$metaColonEqTk? false%$falseTk? )%$rbTk?]? $discr:term with%$withTk
      $alts:matchExprAlts) => do
    let matchExprTk ← fmt matchExprTk
    let optMetaFalse? ← fmtNamedArgumentTerm? lbTk? metaTk? metaColonEqTk? falseTk? rbTk?
    let matchLhs := Layouts.pseudoApplication #[matchExprTk, optMetaFalse?]
    let discr ← fmt discr
    let «match» := Layouts.pseudoApplication #[matchLhs, discr]
    let withTk ← fmt withTk
    let alts ← fmt alts
    return Layouts.keywordSeparated «match» withTk alts {
      allowFlattening := false
      nestedRhs := false
    }
  | _ =>
    throw .partialFormatter

private inductive fmtTryCatchFinally.Handler where
  | doCatch (lhsWithArrow seq : TaggedDoc)
  | doCatchMatch (doc : TaggedDoc)

public def fmtTryCatchFinally
    (stx : Syntax) (tryTk : Syntax) (trySeq : TSyntax ``Parser.Term.doSeq)
    (handlers : Array (TSyntax [``Parser.Term.doCatch, ``Parser.Term.doCatchMatch]))
    (finally? : Option (TSyntax ``Parser.Term.doFinally))
    : FmtM TaggedDoc := do
  let blockCount := 1 + handlers.size + if finally?.isSome then 1 else 0
  let allowFlattening := blockCount <= 2 && !(← hasNewline stx)
  let tryTk ← fmt tryTk
  let trySeq ← fmt trySeq
  let handlers ←
    handlers.mapM fun
      | `(Parser.Term.doCatch| catch%$catchTk $id $[:%$colonTk? $type?:term]? =>%$darrowTk $seq:doSeq) =>
        do
          let catchTk ← fmt catchTk
          let id ← fmt id
          let colonTk? ← fmt? colonTk?
          let type? ← fmt? type?
          let darrowTk ← fmt darrowTk
          let seq ← fmt seq
          let binding := Layouts.typeAscription id colonTk? type?
          let lhs := Layouts.pseudoApplication #[catchTk, binding]
          let lhsWithArrow := Layouts.spacedAtomic #[hardNested lhs, darrowTk]
          return .doCatch lhsWithArrow seq
      | `(Parser.Term.doCatchMatch| catch%$catchTk $alts:matchAlts) => do
        let catchTk ← fmt catchTk
        let alts ← fmt alts
        return .doCatchMatch <| Layouts.matchDeclaration catchTk alts
      | _ =>
        throw .partialFormatter
  let (finallyTk, finallySeq) ← do
    let some «finally» := finally?
      | pure (empty, empty)
    match «finally» with
    | `(Parser.Term.doFinally| finally%$finallyTk $finallySeq:doSeq) =>
      let finallyTk ← fmt finallyTk
      let finallySeq ← fmt finallySeq
      pure (finallyTk, finallySeq)
    | _ =>
      throw .partialFormatter
  if allowFlattening then
    return oneOf #[
      flattened <| mk tryTk trySeq handlers finallyTk finallySeq (allowFlattening := true),
      mk tryTk trySeq handlers finallyTk finallySeq (allowFlattening := false)
    ]
  else
    return unflattenable <| mk tryTk trySeq handlers finallyTk finallySeq (allowFlattening := false)
where
  hasNewline (stx : Syntax) : FmtM Bool := do
    let some pos := stx.getPos?
      | return false
    let some tailPos := stx.getTailPos?
      | return false
    let lineInfos ← getLineInfos pos tailPos
    return lineInfos.size > 1

  mk
      (tryTk trySeq : TaggedDoc) (handlers : Array fmtTryCatchFinally.Handler)
      (finallyTk finallySeq : TaggedDoc) (allowFlattening : Bool)
      : TaggedDoc :=
    let tryBlock := stickyCombine tryTk ⟨nl, nested⟩ trySeq allowFlattening
    let handlerBlocks :=
      handlers.map fun
        | .doCatch lhsWithArrow seq => stickyCombine lhsWithArrow ⟨nl, nested⟩ seq allowFlattening
        | .doCatchMatch doc => doc
    let finallyBlock := stickyCombine finallyTk ⟨nl, nested⟩ finallySeq allowFlattening
    let blocks := #[tryBlock] ++ handlerBlocks ++ #[finallyBlock]
    let blocks := blocks.map fun block => .withSepAfter (some block) nl
    let doc := combine blocks
    if blocks.size > 1 then
      aligned doc
    else
      doc

@[builtin_fmt Lean.Parser.Term.doTry]
public def fmtDoTry : Fmt := fun
  | stx@`(Parser.Term.doTry| try%$tryTk $seq:doSeq $[$handlers]* $[$finally?:doFinally]?) => do
    fmtTryCatchFinally stx tryTk seq handlers finally?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.termTry]
public def fmtTermTry : Fmt := fun
  | stx@`(Parser.Term.termTry| try%$tryTk $seq:doSeq $[$handlers]* $[$finally?:doFinally]?) => do
    fmtTryCatchFinally stx tryTk seq handlers finally?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.doForward]
public def fmtDoForward : Fmt := fun
  | `(Parser.Term.doForward| do%$doTk←%$leftArrowTk $seq:doSeq) => do
    let doTk ← fmt doTk
    let leftArrowTk ← fmt leftArrowTk
    let seq ← fmt seq
    let kw := Layouts.atomic #[doTk, leftArrowTk]
    return Layouts.keywordPrefixedSeq kw seq .sticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.doWhile]
public def fmtDoWhile : Fmt := fun
  | `(Parser.Term.doWhile| while%$whileTk $cond:doIfCond do%$doTk $seq:doSeq) => do
    let whileTk ← fmt whileTk
    let cond ← fmt cond
    let lhs := Layouts.pseudoApplication #[whileTk, cond]
    let doTk ← fmt doTk
    let seq ← fmt seq
    return Layouts.keywordSeparated lhs doTk seq { allowFlattening := false }
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.doRepeatUntil]
public def fmtDoRepeatUntil : Fmt := fun
  | `(Parser.Term.doRepeatUntil| repeat%$repeatTk $seq:doSeq until%$untilTk $cond:term) => do
    let repeatTk ← fmt repeatTk
    let seq ← fmt seq
    let untilTk ← fmt untilTk
    let cond ← fmt cond
    let untilBlock := Layouts.pseudoApplication #[untilTk, cond]
    let repeatBlock := nested <| Layouts.lines #[repeatTk, seq]
    return Layouts.lines #[repeatBlock, untilBlock]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.doNested]
public def fmtDoNested : Fmt := fun
  | `(Parser.Term.doNested| do%$doTk $seq:doSeq) => do
    let doTk ← fmt doTk
    let seq ← fmt seq
    return Layouts.keywordPrefixedSeq doTk seq .sticky
  | _ =>
    throw .partialFormatter
