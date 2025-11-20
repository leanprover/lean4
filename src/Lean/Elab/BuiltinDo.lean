/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Do.Basic
meta import Lean.Parser.Do
import Lean.Meta.ProdN
import Lean.Elab.Do.Control

public section

namespace Lean.Elab.Do

open Lean.Parser.Term
open Lean Parser Meta Elab Do

def getLetIdVars (letId : TSyntax ``letId) : TermElabM (Array Ident) := do
  match letId with
  | `(letId| _) => return #[]
  | `(letId| $id:ident) => return #[id]
  | `(letId| $s:hygieneInfo) => return #[HygieneInfo.mkIdent s `this (canonical := true)]
  | _ => throwError "Not a letId: {letId}"

def getLetIdDeclVars (letIdDecl : TSyntax ``letIdDecl) : TermElabM (Array Ident) := do
  -- def letIdDecl := leading_parser letIdLhs >> " := " >> termParser
  -- def letIdLhs : Parser := letId >> many (ppSpace >> letIdBinder) >> optType
  -- NB: `letIdLhs` does not introduce a new node
  getLetIdVars ⟨letIdDecl.raw[0]⟩

-- support both regular and syntax match
def getPatternVarsEx (pattern : Term) : TermElabM (Array Ident) :=
  open TSyntax.Compat in -- until PatternVar := Ident
  Term.getPatternVars pattern <|>
  Term.Quotation.getPatternVars pattern

def getPatternsVarsEx (patterns : Array Term) : TermElabM (Array Ident) :=
  open TSyntax.Compat in -- until PatternVar := Ident
  Term.getPatternsVars patterns <|>
  Term.Quotation.getPatternsVars patterns

def getExprPatternVarsEx (exprPattern : TSyntax ``matchExprPat) : TermElabM (Array Ident) := do
  let `(matchExprPat| $[$var? @]? $_funName:ident $pvars*) := exprPattern | throwUnsupportedSyntax
  match var? with
  | some var => return #[var] ++ pvars.filter (·.raw.isIdent) |>.map (⟨·⟩)
  | none => return pvars.filter (·.raw.isIdent) |>.map (⟨·⟩)

def getLetPatDeclVars (letPatDecl : TSyntax ``letPatDecl) : TermElabM (Array Ident) := do
  -- def letPatDecl := leading_parser termParser >> pushNone >> optType >> " := " >> termParser
  getPatternVarsEx ⟨letPatDecl.raw[0]⟩

def getLetEqnsDeclVars (letEqnsDecl : TSyntax ``letEqnsDecl) : TermElabM (Array Ident) :=
  -- def letEqnsDecl := leading_parser letIdLhs >> matchAlts
  -- def letIdLhs : Parser := letId >> many (ppSpace >> letIdBinder) >> optType
  -- NB: `letIdLhs` does not introduce a new node
  getLetIdVars ⟨letEqnsDecl.raw[0]⟩

def getLetDeclVars (letDecl : TSyntax ``letDecl) : TermElabM (Array Ident) := do
  match letDecl with
  | `(letDecl| $letIdDecl:letIdDecl) => getLetIdDeclVars letIdDecl
  | `(letDecl| $letPatDecl:letPatDecl) => getLetPatDeclVars ⟨letPatDecl⟩
  | `(letDecl| $letEqnsDecl:letEqnsDecl) => getLetEqnsDeclVars letEqnsDecl
  | _ => throwError "Not a let declaration: {toString letDecl}"

def getLetRecDeclVars (letRecDecl : TSyntax ``letRecDecl) : TermElabM (Array Ident) := do
  -- def letRecDecl := optional docComment >> optional «attributes» >> letDecl >> Termination.suffix
  getLetDeclVars ⟨letRecDecl.raw[2]⟩

def getLetRecDeclsVars (letRecDecls : TSyntax ``letRecDecls) : TermElabM (Array Ident) := do
  -- def letRecDecls := sepBy1 letRecDecl ", "
  let `(letRecDecls| $[$letRecDecls:letRecDecl],*) := letRecDecls | throwUnsupportedSyntax
  let mut allVars := #[]
  for letRecDecl in letRecDecls do
    let vars ← getLetRecDeclVars letRecDecl
    allVars := allVars ++ vars
  return allVars

def getDoLetVars (doLet : TSyntax ``doLet) : TermElabM (Array Ident) :=
  -- def doLet := "let " >> optional "mut " >> letDecl
  match doLet with
  | `(doLet| let $[mut]? $decl:letDecl) => getLetDeclVars decl
  | _ => throwUnsupportedSyntax

def getDoLetElseVars (doLetElse : TSyntax ``doLetElse) : TermElabM (Array Ident) :=
  -- def doLetElse := "let " >> optional "mut " >> termParser >> " := " >> ...
  match doLetElse with
  | `(doLetElse| let $[mut]? $pattern := $_ | $_) => getPatternVarsEx pattern
  | _ => throwUnsupportedSyntax

def getDoHaveVars (doHave : TSyntax ``doHave) : TermElabM (Array Ident) :=
  -- def doHave := "have" >> letDecl
  match doHave with
  | `(doHave| have $decl:letDecl) => getLetDeclVars decl
  | _ => throwUnsupportedSyntax

def getDoLetRecVars (doLetRec : TSyntax ``doLetRec) : TermElabM (Array Ident) := do
  -- def doLetRec := group ("let " >> nonReservedSymbol "rec ") >> letRecDecls
  getLetRecDeclsVars ⟨doLetRec.raw[1]⟩

def getDoIdDeclVar (doIdDecl : TSyntax ``doIdDecl) : TermElabM (Array Ident) :=
  -- def doIdDecl := ident >> optType >> ppSpace >> ...
  getLetIdVars ⟨doIdDecl.raw[0]⟩

def getDoPatDeclVars (doPatDecl : TSyntax ``doPatDecl) : TermElabM (Array Ident) := do
  -- def doPatDecl := termParser >> ppSpace >> leftArrow >> doElemParser >> ...
  getPatternVarsEx ⟨doPatDecl.raw[0]⟩

def getDoLetArrowVars (doLetArrow : TSyntax ``doLetArrow) : TermElabM (Array Ident) := do
  match doLetArrow with
  | `(doLetArrow| let $[mut]? $decl:doIdDecl) => getDoIdDeclVar decl
  | `(doLetArrow| let $[mut]? $decl:doPatDecl) => getDoPatDeclVars decl
  | _ => throwUnsupportedSyntax

def getDoIdOrPatDeclVars (doIdOrPatDecl : TSyntax [``doIdDecl, ``doPatDecl]) : TermElabM (Array Ident) := do
  if doIdOrPatDecl.raw.getKind == ``Parser.Term.letIdDecl then
    getLetIdDeclVars ⟨doIdOrPatDecl⟩
  else if doIdOrPatDecl.raw.getKind == ``Parser.Term.letPatDecl then
    getLetPatDeclVars ⟨doIdOrPatDecl⟩
  else
    throwUnsupportedSyntax

def getDoReassignVars (doReassign : TSyntax ``doReassign) : TermElabM (Array Ident) := do
  -- def doReassign := letIdDeclNoBinders <|> letPatDecl
  getDoIdOrPatDeclVars ⟨doReassign.raw[0]⟩

def getDoReassignArrowVars (doReassignArrow : TSyntax ``doReassignArrow) : TermElabM (Array Ident) := do
  -- def doReassignArrow := doIdDecl <|> doPatDecl
  match doReassignArrow with
  | `(doReassignArrow| $decl:doIdDecl) => getDoIdDeclVar decl
  | `(doReassignArrow| $decl:doPatDecl) => getDoPatDeclVars decl
  | _ => throwUnsupportedSyntax

@[builtin_doElem_elab Lean.Parser.Term.doReturn] def elabDoReturn : DoElab := fun stx _dec => do
  let `(doReturn| return $e) := stx | throwUnsupportedSyntax
  let returnCont ← getReturnCont
  let e ← elabTermEnsuringType e returnCont.resultType
  mapLetDeclZeta returnCont.resultName returnCont.resultType e fun _ =>
    returnCont.k

@[builtin_doElem_elab Lean.Parser.Term.doBreak] def elabDoBreak : DoElab := fun _stx _dec => do
  let some breakCont := (← getBreakCont)
    | throwError "`break` must be nested inside a loop"
  breakCont

@[builtin_doElem_elab Lean.Parser.Term.doContinue] def elabDoContinue : DoElab := fun _stx _dec => do
  let some continueCont := (← getContinueCont)
    | throwError "`continue` must be nested inside a loop"
  continueCont

@[builtin_doElem_elab Lean.Parser.Term.doExpr] def elabDoExpr : DoElab := fun stx dec => do
  let `(doExpr| $e:term) := stx | throwUnsupportedSyntax
  let mα ← mkMonadicType dec.resultType
  let e ← elabTermEnsuringType e mα
  dec.mkBindUnlessPure e

@[builtin_doElem_elab Lean.Parser.Term.doNested] def elabDoNested : DoElab := fun stx dec => do
  let `(doNested| do $doSeq) := stx | throwUnsupportedSyntax
  elabDoSeq ⟨doSeq.raw⟩ dec

inductive LetOrReassign
  | let (mutTk? : Option Syntax)
  | have
  | reassign

def LetOrReassign.getLetMutTk? (letOrReassign : LetOrReassign) : Option Syntax :=
  match letOrReassign with
  | .let mutTk? => mutTk?
  | .have => none
  | .reassign => none

def LetOrReassign.checkMutVars (letOrReassign : LetOrReassign) (vars : Array Ident) : DoElabM Unit :=
  match letOrReassign with
  | .let _    => checkMutVarsForShadowing vars
  | .have => checkMutVarsForShadowing vars
  | .reassign => throwUnlessMutVarsDeclared vars

@[inline]
def LetOrReassign.ensureReassignsPreserveType (letOrReassign : LetOrReassign) (vars : Array Ident) : MetaM (TermElabM Unit) := do
  match letOrReassign with
  | .let _    => return pure ()
  | .have => return pure ()
  | .reassign => do
    let decls := (← getLCtx).findFromUserNames (.ofArray <| vars.map (·.getId))
    return do
      for var in vars do
        let fvar ← getFVarFromUserName var.getId
        let some decl := decls.find? (fun (decl : LocalDecl) => decl.userName == var.getId)
          | continue
        discard <| Term.ensureHasType decl.type fvar

def elabDoLetOrReassignWith (letOrReassign : LetOrReassign) (vars : Array Ident)
    (dec : DoElemCont) (elabBody : (body : Term) → TermElabM Expr) : DoElabM Expr := do
  letOrReassign.checkMutVars vars
  let ensure ← letOrReassign.ensureReassignsPreserveType vars
  controlAtTermElabM fun runInBase => do
    let elabCont : TermElabM Expr := do
      ensure
      runInBase <| declareMutVars? letOrReassign.getLetMutTk? vars dec.continueWithUnit
    Term.elabToSyntax (fun _ty? => elabCont) fun body => elabBody body

def elabDoLetOrReassign (letOrReassign : LetOrReassign) (decl : TSyntax ``letDecl)
    (dec : DoElemCont) : DoElabM Expr := do
  let vars ← getLetDeclVars decl
  let mγ ← mkMonadicType (← read).doBlockResultType
  elabDoLetOrReassignWith letOrReassign vars dec fun body => do
    Term.elabLetDecl (← `(let $decl:letDecl; $body)) mγ

def elabDoLetOrReassignElse (letOrReassign : LetOrReassign) (pattern rhs : Term)
    (otherwise : TSyntax ``doSeq) (dec : DoElemCont) : DoElabM Expr := do
  let vars ← getPatternVarsEx pattern
  let γ := (← read).doBlockResultType
  let mγ ← mkMonadicType γ
  let otherwise ← elabDoSeq otherwise (← DoElemCont.mkPure γ)
  let otherwise ← Term.exprToSyntax otherwise
  elabDoLetOrReassignWith letOrReassign vars dec fun body => do
    Term.elabMatch (← `(match $rhs:term with | $pattern => $body | _ => $otherwise)) mγ

def elabDoIdDecl (x : Ident) (xType? : Option Term) (rhs : TSyntax `doElem) (k : DoElabM Expr) : DoElabM Expr := do
  let xType ← elabType xType?
  let lctx ← getLCtx
  let ctx ← read
  elabDoElem rhs <| .mk x.getId xType do
    withLCtxKeepingMutVarDefs lctx ctx x.getId k

def elabDoArrow (letOrReassign : LetOrReassign) (stx : TSyntax [``doIdDecl, ``doPatDecl]) (dec : DoElemCont) : DoElabM Expr := do
  match stx with
  | `(doIdDecl| $x:ident ← $rhs) =>
    letOrReassign.checkMutVars #[x]
    elabDoIdDecl x none rhs (declareMutVar? letOrReassign.getLetMutTk? x dec.continueWithUnit)
  | `(doPatDecl| $pattern:term ← $rhs $[| $otherwise?]?) =>
    let x ← Term.mkFreshIdent pattern
    elabDoIdDecl x none rhs do
      match letOrReassign, otherwise? with
      | .let mutTk?, none =>
        elabDoElem (← `(doElem| let $[mut%$mutTk?]? $pattern:term := $x)) dec
      | .let mutTk?, some otherwise =>
        elabDoElem (← `(doElem| let $[mut%$mutTk?]? $pattern:term := $x | $otherwise)) dec
      | .have, none =>
        elabDoElem (← `(doElem| have $pattern:term := $x)) dec
      | .have, some _otherwise =>
        throwUnsupportedSyntax
      | .reassign, none =>
        elabDoElem (← `(doElem| $pattern:term := $x)) dec
      | .reassign, some otherwise =>
        throwError (Function.const _ "doReassignElse needs a stage0 update for quotation syntax" otherwise)
        elabDoElem ⟨← `(doReassignElse| $pattern:term := $x | $otherwise)⟩ dec
  | _ => throwUnsupportedSyntax

@[builtin_doElem_elab Lean.Parser.Term.doLet] def elabDoLet : DoElab := fun stx dec => do
  let `(doLet| let $[mut%$mutTk?]? $decl:letDecl) := stx | throwUnsupportedSyntax
  elabDoLetOrReassign (.let mutTk?) decl dec

@[builtin_doElem_elab Lean.Parser.Term.doHave] def elabDoHave : DoElab := fun stx dec => do
  let `(doHave| have $decl:letDecl) := stx | throwUnsupportedSyntax
  elabDoLetOrReassign .have decl dec

@[builtin_doElem_elab Lean.Parser.Term.doReassign] def elabDoReassign : DoElab := fun stx dec => do
  -- def doReassign := letIdDeclNoBinders <|> letPatDecl
  -- And `letIdDeclNoBinders` is a `letIdDecl`. We wrap a `letDecl` node manually.
  let decl : TSyntax ``letDecl := ⟨mkNode ``letDecl #[stx.raw[0]]⟩
  elabDoLetOrReassign .reassign decl dec

@[builtin_doElem_elab Lean.Parser.Term.doLetElse] def elabDoLetElse : DoElab := fun stx dec => do
  let `(doLetElse| let $[mut%$mutTk?]? $pattern := $rhs | $otherwise) := stx | throwUnsupportedSyntax
  elabDoLetOrReassignElse (.let mutTk?) pattern rhs otherwise dec

@[builtin_doElem_elab Lean.Parser.Term.doReassignElse] def elabDoReassignElse : DoElab := fun stx dec => do
  let `(doReassignElse| $pattern := $rhs | $otherwise) := stx | throwUnsupportedSyntax
  elabDoLetOrReassignElse .reassign pattern rhs otherwise dec

@[builtin_doElem_elab Lean.Parser.Term.doLetArrow] def elabDoLetArrow : DoElab := fun stx dec => do
  let `(doLetArrow| let $[mut%$mutTk?]? $decl) := stx | throwUnsupportedSyntax
  elabDoArrow (.let mutTk?) decl dec

@[builtin_doElem_elab Lean.Parser.Term.doReassignArrow] def elabDoReassignArrow : DoElab := fun stx dec => do
  match stx with
  | `(doReassignArrow| $decl:doIdDecl) =>
    elabDoArrow .reassign decl dec
  | `(doReassignArrow| $decl:doPatDecl) =>
    elabDoArrow .reassign decl dec
  | _ => throwUnsupportedSyntax

@[builtin_doElem_elab Lean.Parser.Term.doIf] def elabDoIf : DoElab := fun stx dec => do
  let `(doIf|if $cond:doIfCond then $thenSeq $[else if $conds:doIfCond then $thenSeqs]* $[else $elseSeq?]?) := stx | throwUnsupportedSyntax
  let mγ ← mkMonadicType (← read).doBlockResultType
  dec.withDuplicableCont fun dec => do
  let mut (res : Expr) ← match elseSeq? with
    | some elseSeq => elabDoSeq elseSeq dec
    | none         => dec.continueWithUnit
  for (cond, thenSeq) in Array.zip (conds.reverse.push cond) (thenSeqs.reverse.push thenSeq) do
    let resStx ← Term.exprToSyntax res
    let withThenStx k := controlAtTermElabM fun runInBase =>
      Term.elabToSyntax (fun _ => runInBase <| elabDoSeq thenSeq dec) k
    res ← match cond with
    | `(doIfCond|let $pat ← $rhs) => do
      let x ← Term.mkFreshIdent pat
      elabDoIdDecl x none (← `(doElem| $rhs:term)) do withThenStx fun thenStx => do
        Term.elabTerm (← `(match $x:term with | $pat => $thenStx | _ => $resStx)) mγ
    | `(doIfCond|let $pat := $d) => withThenStx fun thenStx => do
      Term.elabMatch (← `(match $d:term with | $pat => $thenStx | _ => $resStx)) mγ
    | `(doIfCond|$cond) => withThenStx fun thenStx => do
      Term.elabTerm (← `(if $cond then $thenStx else $resStx)) mγ
    | `(doIfCond|$h : $cond) => withThenStx fun thenStx => do
      Term.elabTerm (← `(if $h:ident : $cond then $thenStx else $resStx)) mγ
    | _ => throwUnsupportedSyntax
  return res

@[builtin_doElem_elab Lean.Parser.Term.doMatch] def elabDoMatch : DoElab := fun stx dec => do
  let `(doMatch| match $[$gen]? $[$motive]? $discrs,* with $alts:matchAlt*) := stx | throwUnsupportedSyntax
  -- cf. `expandMatchAlts?`
  let alts : Array (TSyntax ``Term.matchAlt) :=
    if alts.any Term.shouldExpandMatchAlt then
      alts.foldl (init := #[]) fun alts alt =>
        alts ++ (Term.expandMatchAlt alt)
    else
      alts
  let mγ ← mkMonadicType (← read).doBlockResultType
  dec.withDuplicableCont fun dec => do
  controlAtTermElabM fun runInBase => do
    let rec elabMatch i (alts : Array (TSyntax ``Term.matchAlt)) := do
      if h : i < alts.size then
        match alts[i] with
        | `(matchAltExpr| | $patterns,* => $seq) =>
          let vars ← getPatternsVarsEx patterns
          runInBase <| checkMutVarsForShadowing vars
          Term.elabToSyntax (fun _ => runInBase <| elabDoSeq ⟨seq⟩ dec) fun rhs => do
            elabMatch (i + 1) (alts.set i (← `(matchAltExpr| | $patterns,* => $rhs)))
        | _ => throwUnsupportedSyntax
      else
        Term.elabMatch (← `(match $[$gen]? $[$motive]? $discrs,* with $alts:matchAlt*)) mγ
    elabMatch 0 alts

@[builtin_doElem_elab Lean.Parser.Term.doMatchExpr] def elabDoMatchExpr : DoElab := fun stx dec => do
  let `(doMatchExpr| match_expr $[(meta := false)%$metaFalseTk?]? $discr:term with $alts) := stx | throwUnsupportedSyntax
  if metaFalseTk?.isNone then -- i.e., implicitly (meta := true)
    let x ← Term.mkFreshIdent discr
    elabDoIdDecl x none (← `(doElem| instantiateMVars $discr)) do
      elabDoMatchExprNoMeta x alts dec
  else
    elabDoMatchExprNoMeta discr alts dec
where elabDoMatchExprNoMeta (discr : Term) (alts : TSyntax ``Term.matchExprAlts) (dec : DoElemCont) : DoElabM Expr := do
  let mγ ← mkMonadicType (← read).doBlockResultType
  dec.withDuplicableCont fun dec => do
  controlAtTermElabM fun runInBase => do
    let rec elabMatch i (altsArr : Array (TSyntax ``Term.matchExprAlt)) := do
      if h : i < altsArr.size then
        match altsArr[i] with
        | `(matchExprAltExpr| | $pattern => $seq) =>
          let vars ← getExprPatternVarsEx pattern
          runInBase <| checkMutVarsForShadowing vars
          Term.elabToSyntax (fun _ => runInBase <| elabDoSeq ⟨seq⟩ dec) fun rhs => do
            elabMatch (i + 1) (altsArr.set i (← `(matchExprAltExpr| | $pattern => $rhs)))
        | _ => throwUnsupportedSyntax
      else
        let alts : TSyntax ``Term.matchExprAlts := ⟨alts.raw.modifyArg 0 fun node => node.setArgs altsArr⟩
        Term.elabTerm (← `(match_expr $discr with $alts)) mγ
    elabMatch 0 (alts.raw[0].getArgs.map (⟨·⟩))

@[builtin_doElem_elab Lean.Parser.Term.doLetExpr] def elabDoLetExpr : DoElab := fun stx dec => do
  let `(doLetExpr| let_expr $pattern:matchExprPat := $rhs:term | $otherwise) := stx | throwUnsupportedSyntax
  let γ := (← read).doBlockResultType
  let mγ ← mkMonadicType γ
  let otherwise ← elabDoSeq otherwise (← DoElemCont.mkPure γ)
  let otherwise ← Term.exprToSyntax otherwise
  controlAtTermElabM fun runInBase => do
    let vars ← getExprPatternVarsEx pattern
    runInBase <| checkMutVarsForShadowing vars
    Term.elabToSyntax (fun _ => runInBase <| dec.continueWithUnit) fun body => do
      Term.elabTerm (← `(match_expr $rhs with | $pattern => $body | _ => $otherwise)) mγ

@[builtin_doElem_elab Lean.Parser.Term.doLetMetaExpr] def elabDoLetMetaExpr : DoElab := fun stx dec => do
  let `(doLetMetaExpr| let_expr $pattern:matchExprPat ← $rhs:term | $otherwise) := stx | throwUnsupportedSyntax
  let x ← Term.mkFreshIdent pattern
  elabDoIdDecl x none (← `(doElem| instantiateMVars $rhs)) do
    elabDoLetExpr (← `(doElem| let_expr $pattern:matchExprPat := $x | $otherwise)) dec

@[builtin_doElem_elab Lean.Parser.Term.doUnless] def elabDoUnless : DoElab := fun stx dec => do
  let `(doUnless| unless $cond do $body) := stx | throwUnsupportedSyntax
  let γ := (← read).doBlockResultType
  let mγ ← mkMonadicType γ
  let else_ ← elabDoSeq body (← DoElemCont.mkPure γ)
  let then_ ← dec.continueWithUnit
  let else_ ← Term.exprToSyntax else_
  let then_ ← Term.exprToSyntax then_
  Term.elabTerm (← `(if $cond then $then_ else $else_)) mγ

@[builtin_doElem_elab Lean.Parser.Term.doDbgTrace] def elabDoDbgTrace : DoElab := fun stx dec => do
  let `(doDbgTrace| dbg_trace $msg:term) := stx | throwUnsupportedSyntax
  let mγ ← mkMonadicType (← read).doBlockResultType
  let body ← dec.continueWithUnit
  let body ← Term.exprToSyntax body
  Term.elabTerm (← `(dbg_trace $msg; $body)) mγ

@[builtin_doElem_elab Lean.Parser.Term.doAssert] def elabDoAssert : DoElab := fun stx dec => do
  let `(doAssert| assert! $cond) := stx | throwUnsupportedSyntax
  let mγ ← mkMonadicType (← read).doBlockResultType
  let body ← dec.continueWithUnit
  let body ← Term.exprToSyntax body
  Term.elabTerm (← `(assert! $cond; $body)) mγ

@[builtin_doElem_elab Lean.Parser.Term.doDebugAssert] def elabDoDebugAssert : DoElab := fun stx dec => do
  let `(doDebugAssert| debug_assert! $cond) := stx | throwUnsupportedSyntax
  let mγ ← mkMonadicType (← read).doBlockResultType
  let body ← dec.continueWithUnit
  let body ← Term.exprToSyntax body
  Term.elabTerm (← `(debug_assert! $cond; $body)) mγ

@[builtin_macro Lean.Parser.Term.doFor] def expandDoFor : Macro := fun stx => do
  match stx with
  | `(doFor| for $[$_ : ]? $_:ident in $_ do $_) =>
    -- This is the target form of the expander, handled by `elabDoFor` below.
    Macro.throwUnsupported
  | `(doFor| for $decls:doForDecl,* do $body) =>
    let decls := decls.getElems
    let `(doForDecl| $[$h? : ]? $pattern in $xs) := decls[0]! | Macro.throwUnsupported
    let mut doElems := #[]
    let mut body := body
    -- Expand `pattern` into an `Ident` `x`:
    let x ←
      if pattern.raw.isIdent then
        pure ⟨pattern⟩
      else
        let x ← Term.mkFreshIdent pattern
        body ← `(doSeq| match $x:term with | $pattern => $body)
        pure x
    -- Expand the remaining `doForDecl`s:
    for doForDecl in decls[1...*] do
      /-
        Expand
        ```
        for x in xs, y in ys do
          body
        ```
        into
        ```
        let mut s := Std.toStream ys
        for x in xs do
          match Std.Stream.next? s with
          | none => break
          | some (y, s') =>
            s := s'
            body
        ```
      -/
      let `(doForDecl| $[$h? : ]? $y in $ys) := doForDecl | Macro.throwUnsupported
      if let some h := h? then
        Macro.throwErrorAt h "The proof annotation here has not been implemented yet."
      /- Recall that `@` (explicit) disables `coeAtOutParam`.
         We used `@` at `Stream` functions to make sure `resultIsOutParamSupport` is not used. -/
      let toStreamApp ← withRef ys `(@Std.toStream _ _ _ $ys)
      let s ← Term.mkFreshIdent ys
      doElems := doElems.push (← `(doSeqItem| let mut $s := $toStreamApp:term))
      body ← `(doSeq|
        match @Std.Stream.next? _ _ _ $s with
          | none => break
          | some ($y, s') =>
            $s:ident := s'
            do $body)
    doElems := doElems.push (← `(doSeqItem| for $[$h? : ]? $x:ident in $xs do $body))
    `(doElem| do $doElems*)
  | _ => Macro.throwUnsupported

@[builtin_doElem_elab Lean.Parser.Term.doFor] def elabDoFor : DoElab := fun stx dec => do
  let `(doFor| for $[$h? : ]? $x:ident in $xs do $body) := stx | throwUnsupportedSyntax
  let uα ← mkFreshLevelMVar
  let uρ ← mkFreshLevelMVar
  let α ← mkFreshExprMVar (mkSort (mkLevelSucc uα)) (userName := `α)
  let ρ ← mkFreshExprMVar (mkSort (mkLevelSucc uρ)) (userName := `ρ)
  let xs ← elabTermEnsuringType xs ρ
  let mi := (← read).monadInfo
  let σ ← mkFreshExprMVar (mkSort (mkLevelSucc mi.u)) (userName := `σ)
  let γ := (← read).doBlockResultType
  let β ← mkArrow σ (← mkMonadicType γ)
  let mutVars := (← read).mutVars
  let breakRhs ← mkFreshExprMVar β
  let (app, p?) ← match h? with
    | none =>
      let instForIn ← Term.mkInstMVar <| mkApp3 (mkConst ``ForInNew [uρ, uα, mi.u, mi.v]) mi.m ρ α
      let app := mkConst ``ForInNew.forIn [uρ, uα, mi.u, mi.v]
      let app := mkApp7 app mi.m ρ α instForIn σ γ xs -- 3 args remaining: preS, kcons, knil
      pure (app, none)
    | some _ =>
      let p ← mkFreshExprMVar (← mkArrowN #[ρ, α] (mkSort .zero)) (userName := `p)
      let instForIn ← Term.mkInstMVar <| mkApp4 (mkConst ``ForInNew' [uρ, uα, mi.u, mi.v]) mi.m ρ α p
      let app := mkConst ``ForInNew'.forIn' [uρ, uα, mi.u, mi.v]
      let app := mkApp8 app mi.m ρ α p instForIn σ γ xs -- 3 args remaining: preS, kcons, knil
      pure (app, some p)
  withLetDecl (← mkFreshUserName `kbreak) β breakRhs (kind := .implDetail) (nondep := true) fun kbreak => do
  let xh : Array (Name × (Array Expr → DoElabM Expr)) := match h?, p? with
    | some h, some p => #[(x.getId, fun _ => pure α), (h.getId, fun x => pure (mkApp2 p xs x[0]!))]
    | _, _ => #[(x.getId, fun _ => pure α)]
  withLocalDeclsD xh fun xh => do
  withLocalDecl (← mkFreshUserName `kcontinue) .default β (kind := .implDetail) fun kcontinue => do
  withLocalDecl (← mkFreshUserName `s) .default σ (kind := .implDetail) fun loopS => do
  withProxyMutVarDefs fun elimProxyDefs => do
    let rootCtx ← getLCtx
    -- We will use `continueKVar` to stand in for the `DoElemCont` `dec` below.
    -- Adding `dec.resultName` to the list of tunneled vars helps with some MVar assignment issues.
    let continueKVar ← mkFreshContVar γ (mutVars.push dec.resultName)
    let breakKVar ← mkFreshContVar γ mutVars

    -- Elaborate the loop body, which must have result type `PUnit`.
    let body ← enterLoopBody γ (← getReturnCont) breakKVar.mkJump continueKVar.mkJump do
      elabDoSeq body { dec with k := continueKVar.mkJump }

    -- Compute the set of mut vars that were reassigned on the path to a back jump (`continue`).
    -- Take care to preserve the declaration order that is manifest in the array `mutVars`.
    let loopMutVars ← do
      let ctn ← continueKVar.getReassignedMutVars rootCtx
      let brk ← breakKVar.getReassignedMutVars rootCtx
      pure (ctn.union brk)
    let loopMutVars := mutVars.filter loopMutVars.contains

    -- Assign the state tuple type and the initial tuple of states.
    let preS ← σ.mvarId!.withContext do
      let defs ← loopMutVars.mapM (getFVarFromUserName ·)
      let (tuple, tupleTy) ← mkProdMkN defs
      synthUsingDefEq "state tuple type" σ tupleTy
      pure tuple

    -- Synthesize the `continue` and `break` jumps.
    continueKVar.synthesizeJumps do
      let (tuple, _tupleTy) ← mkProdMkN (← loopMutVars.mapM (getFVarFromUserName ·))
      return mkApp kcontinue tuple
    breakKVar.synthesizeJumps do
      let (tuple, _tupleTy) ← mkProdMkN (← loopMutVars.mapM (getFVarFromUserName ·))
      return mkApp kbreak tuple

    -- Elaborate the continuation, now that `σ` is known. It will be the `break` handler.
    -- If there is a `break`, the code will be shared in the `kbread` join point.
    breakRhs.mvarId!.withContext do
      let e ← withLocalDeclD (← mkFreshUserName `s) σ fun postS => do mkLambdaFVars #[postS] <| ← do
        bindMutVarsFromTuple loopMutVars.toList postS.fvarId! do
          dec.continueWithUnit
      synthUsingDefEq "break RHS" breakRhs e

    -- Finally eliminate the proxy variables from the loop body.
    -- * Point non-reassigned mut var defs to the pre state
    -- * Point the initial defs of reassigned mut vars to the loop state
    -- Done by `elimProxyDefs` below.
    let body ← bindMutVarsFromTuple loopMutVars.toList loopS.fvarId! do
      elimProxyDefs body

    let hadBreak := (← breakKVar.jumpCount) > 0
    let kcons ← mkLambdaFVars (xh ++ #[kcontinue, loopS]) body
    let knil := if hadBreak then kbreak else breakRhs
    let app := mkApp3 app preS kcons knil
    if hadBreak then
      mkLetFVars (generalizeNondepLet := false) #[kbreak] app
    else
      return (← elimMVarDeps #[kbreak] app).replaceFVar kbreak breakRhs


@[builtin_doElem_elab Lean.Parser.Term.doTry] def elabDoTry : DoElab := fun stx dec => do
  let `(doTry| try $trySeq:doSeq $[$catches]* $[finally $finSeq?]?) := stx | throwUnsupportedSyntax
--  let `(doTry| try $trySeq:doSeq $[catch $xs $[: $eTypes?]? => $catchSeqs]* $[finally $finSeq?]?) := stx | throwUnsupportedSyntax
  checkMutVarsForShadowing <| catches.filterMap (fun | `(doCatch| catch $x:ident $[: $_]? => $_) => some x | _ => none)
  if catches.isEmpty && finSeq?.isNone then
    throwError "Invalid `try`. There must be a `catch` or `finally`."
  -- We cannot use join points because `tryCatch` and `tryFinally` are never tail-resumptive.
  -- (Proof: `do tryCatch e h; throw x ≠ tryCatch (do e; throw x) (fun e => do h e; throw x)`)
  -- This is also known as the "algebraicity property" in the algebraic effects and handlers
  -- community.
  --
  -- So we need to pack up our effects and unpack them after the `try`.
  -- We could optimize for the `.last` case by omitting the state tuple ... in the future.
  let mi := (← read).monadInfo
  let lifter ← Lean.Elab.Do.ControlLifter.ofCont dec
  let body ← lifter.lift (elabDoSeq trySeq)
  let body ← catches.foldlM (init := body) fun body catch_ => do
    let `(doCatch| catch $x $[: $eType?]? => $catchSeq) := catch_ | throwUnsupportedSyntax
    let x := Term.mkExplicitBinder x <| match eType? with
      | some eType => eType
      | none => mkHole x
    let (catch_, ε, uε) ← elabBinder x fun x => do
      let ε ← inferType x
      let uε ← getDecLevel ε
      let catch_ ← lifter.lift (elabDoSeq catchSeq)
      let catch_ ← mkLambdaFVars #[x] catch_
      return (catch_, ε, uε)
    if eType?.isSome then
      let inst ← Term.mkInstMVar <| mkApp2 (mkConst ``MonadExceptOf [uε, mi.u, mi.v]) ε mi.m
      return mkApp6 (mkConst ``tryCatchThe [uε, mi.u, mi.v])
        ε mi.m inst lifter.resultType body catch_
    else
      let inst ← Term.mkInstMVar <| mkApp2 (mkConst ``MonadExcept [uε, mi.u, mi.v]) ε mi.m
      return mkApp6 (mkConst ``MonadExcept.tryCatch [uε, mi.u, mi.v])
        ε mi.m inst lifter.resultType body catch_
  let body ← match finSeq? with
    | none => pure body
    | some finSeq => do
      let β ← mkFreshResultType `β
      let fin ← enterFinally β <| elabDoSeq finSeq (← DoElemCont.mkPure β)
      let instMonadFinally ← Term.mkInstMVar <| mkApp (mkConst ``MonadFinally [mi.u, mi.v]) mi.m
      let instFunctor ← Term.mkInstMVar <| mkApp (mkConst ``Functor [mi.u, mi.v]) mi.m
      pure <| mkApp7 (mkConst ``tryFinally [mi.u, mi.v])
        mi.m lifter.resultType β instMonadFinally instFunctor body fin
  (← lifter.restoreCont).mkBindUnlessPure body
