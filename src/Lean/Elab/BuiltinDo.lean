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
  | `(doLetElse| let $[mut]? $pattern := $_ | $_ $_:doSeq) => getPatternVarsEx pattern
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

@[builtin_doElem_elab Lean.Parser.Term.doReturn] def elabDoReturn : DoElab := fun stx dec => do
  let `(doReturn| return $[$e?]?) := stx | throwUnsupportedSyntax
  let returnCont ← getReturnCont
  let e ← match e? with
    | some e => Term.elabTermEnsuringType e returnCont.resultType
    | none   => mkPUnitUnit
  dec.elabAsDeadCode -- emit dead code warnings
  returnCont.k e

@[builtin_doElem_elab Lean.Parser.Term.doBreak] def elabDoBreak : DoElab := fun _stx dec => do
  let some breakCont := (← getBreakCont)
    | throwError "`break` must be nested inside a loop"
  dec.elabAsDeadCode -- emit dead code warnings
  breakCont

@[builtin_doElem_elab Lean.Parser.Term.doContinue] def elabDoContinue : DoElab := fun _stx dec => do
  let some continueCont := (← getContinueCont)
    | throwError "`continue` must be nested inside a loop"
  dec.elabAsDeadCode -- emit dead code warnings
  continueCont

@[builtin_doElem_elab Lean.Parser.Term.doExpr] def elabDoExpr : DoElab := fun stx dec => do
  let `(doExpr| $e:term) := stx | throwUnsupportedSyntax
  let mα ← mkMonadicType dec.resultType
  let e ← Term.elabTermEnsuringType e mα
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
  | _           => none

def LetOrReassign.checkMutVars (letOrReassign : LetOrReassign) (vars : Array Ident) : DoElabM Unit :=
  match letOrReassign with
  | .reassign => throwUnlessMutVarsDeclared vars
  | _         => checkMutVarsForShadowing vars

@[inline]
def LetOrReassign.registerReassignAliasInfo (letOrReassign : LetOrReassign) (vars : Array Ident) : DoElabM Unit := do
  if letOrReassign matches .reassign then
    let mutVarDefs := (← read).mutVarDefs
    for var in vars do
      if let some baseId := mutVarDefs[var.getId]? then
        let id := (← getFVarFromUserName var.getId).fvarId!
        if id != baseId then
          pushInfoLeaf <| .ofFVarAliasInfo { userName := var.getId, id, baseId }

def elabDoLetOrReassignWith (hint : MessageData) (letOrReassign : LetOrReassign) (vars : Array Ident)
    (k : DoElabM Expr) (elabBody : (body : Term) → TermElabM Expr) : DoElabM Expr := do
  -- letOrReassign.checkMutVars vars -- Should be done by the caller!
  let elabCont : DoElabM Expr := do
    declareMutVars? letOrReassign.getLetMutTk? vars do
      letOrReassign.registerReassignAliasInfo vars
      k
  doElabToSyntax hint elabCont fun body => elabBody body

def elabWithReassignments (letOrReassign : LetOrReassign) (vars : Array Ident) (k : DoElabM Expr) : DoElabM Expr := do
  declareMutVars? letOrReassign.getLetMutTk? vars do
    letOrReassign.registerReassignAliasInfo vars
    k

def elabDoLetOrReassign (letOrReassign : LetOrReassign) (decl : TSyntax ``letDecl)
    (dec : DoElemCont) : DoElabM Expr := do
  let vars ← getLetDeclVars decl
  letOrReassign.checkMutVars vars
  let mγ ← mkMonadicType (← read).doBlockResultType
  -- For plain variable reassignment, we infer the LHS as a term and use that as the expected type
  -- of the RHS:
  let decl ←
    if letOrReassign matches .reassign then
      match decl with
      | `(letDecl| $x:ident $[: $xType?]? := $rhs) =>
        -- We use `Term.elabTermEnsuringType` instead of `Term.ensureHasType` to turn type
        -- mismatches into sorrys.
        discard <| Term.elabTermEnsuringType (← `($x:ident)) (← xType?.mapM (Term.elabType ·))
        let xType ← Term.exprToSyntax (← getLocalDeclFromUserName x.getId).type
        `(letDecl| $x:ident : $xType := $rhs)
      | `(letDecl| $pattern:term $[: $xType?]? := $rhs) =>
        let pattern ← match xType? with
          | some xType => `(($pattern : $xType))
          | none       => pure pattern
        -- `Term.withoutErrToSorry` prevents a confusing secondary error message when elaborating
        -- the `match` pattern, where the mut vars potentially get a different type.
        -- Example: `let mut n : Nat := 0; ((n : Char), _) := (false, false)`. We don't want to see
        --          "`n` has type `Char` but was expected to have type `Bool`".
        let e ← Term.withoutErrToSorry <| Term.elabTerm pattern none
        let patType ← Term.exprToSyntax (← inferType e)
        `(letDecl| $pattern:term := ($rhs : $patType))
      | _ => throwError m!"Impossible case in elabDoLetOrReassign. This is an elaborator bug.\n{decl}"
    else
      pure decl
  let contElab : DoElabM Expr := elabWithReassignments letOrReassign vars dec.continueWithUnit
  doElabToSyntax m!"let body of {vars}" contElab fun body => do
    match letOrReassign with
    | .have => Term.elabHaveDecl (← `(have $decl:letDecl; $body)) mγ
    | _     => Term.elabLetDecl (← `(let $decl:letDecl; $body)) mγ

def elabDoLetOrReassignElse (letOrReassign : LetOrReassign) (pattern rhs : Term)
    (body otherwise : TSyntax ``doSeq) (dec : DoElemCont) : DoElabM Expr := do
  let vars ← getPatternVarsEx pattern
  letOrReassign.checkMutVars vars
  -- For plain variable reassignment, we infer the LHS as a term and use that as the expected type
  -- of the RHS:
  let pattern ←
    if letOrReassign matches .reassign then
      let e ← Term.withoutErrToSorry <| Term.elabTerm pattern none
      let patType ← Term.exprToSyntax (← inferType e)
      `(($pattern : $patType))
    else
      pure pattern
  dec.withDuplicableCont fun dec => do
  let otherwiseElab := elabDoSeq otherwise dec
  let bodyElab := elabWithReassignments letOrReassign vars (elabDoSeq body dec)
  doElabToSyntax m!"else case of {pattern}" otherwiseElab fun otherwise => do
  doElabToSyntax m!"let body of {pattern}" bodyElab fun body => do
    let mγ ← mkMonadicType (← read).doBlockResultType
    Term.elabTerm (← `(match (generalizing := false) (motive := ∀ _, $(← Term.exprToSyntax mγ)) $rhs:term with
                       | $pattern => $body
                       | _ => $otherwise)) mγ

def elabDoIdDecl (x : Ident) (xType? : Option Term) (rhs : TSyntax `doElem) (contRef : Syntax) (k : DoElabM Expr)
    (kind : DoElemContKind := .nonDuplicable) (declKind : LocalDeclKind := .default) : DoElabM Expr := do
  let xType ← Term.elabType (xType?.getD (mkHole x))
  let lctx ← getLCtx
  let ctx ← read
  elabDoElem rhs <| .mk (kind := kind) (declKind := declKind) (ref := contRef) x.getId xType do
    withLCtxKeepingMutVarDefs lctx ctx x.getId do
      Term.addLocalVarInfo x (← getFVarFromUserName x.getId)
      k

def elabDoArrow (letOrReassign : LetOrReassign) (stx : TSyntax [``doIdDecl, ``doPatDecl]) (dec : DoElemCont) : DoElabM Expr := do
  match stx with
  | `(doIdDecl| $x:ident $[: $xType?]? ← $rhs) =>
    letOrReassign.checkMutVars #[x]
    -- For plain variable reassignment, we know the expected type of the reassigned variable and
    -- propagate it eagerly via type ascription if the user hasn't provided one themselves:
    let xType? ← match letOrReassign, xType? with
      | .reassign, none =>
        let decl ← getLocalDeclFromUserName x.getId
        some <$> Term.exprToSyntax decl.type
      | _, _ => pure xType?
    elabDoIdDecl x xType? rhs (declareMutVar? letOrReassign.getLetMutTk? x dec.continueWithUnit)
      (kind := dec.kind) (contRef := dec.ref)
  | `(doPatDecl| $pattern:term ← $rhs $[| $otherwise?:doSeq $rest?:doSeq]?) =>
    let x ← Term.mkFreshIdent pattern
    elabDoIdDecl x none rhs (contRef := pattern) (declKind := .implDetail) do
      match letOrReassign, otherwise?, rest? with
      | .let mutTk?, some otherwise, some rest =>
        elabDoElem (← `(doElem| let $[mut%$mutTk?]? $pattern:term := $x | $otherwise:doSeq $rest:doSeq)) dec
      | .let mutTk?, _, _ =>
        elabDoElem (← `(doElem| let $[mut%$mutTk?]? $pattern:term := $x)) dec
      | .have, some _otherwise, some _rest =>
        throwUnsupportedSyntax
      | .have, _, _ =>
        elabDoElem (← `(doElem| have $pattern:term := $x)) dec
      | .reassign, some otherwise, some rest =>
        throwError (Function.const _ "doReassignElse needs a stage0 update for quotation syntax" otherwise)
        elabDoElem ⟨← `(doReassignElse| $pattern:term := $x | $otherwise:doSeq $rest:doSeq)⟩ dec
      | .reassign, _, _ =>
        elabDoElem (← `(doElem| $pattern:term := $x)) dec
  | _ => throwUnsupportedSyntax

@[builtin_doElem_elab Lean.Parser.Term.doLet] def elabDoLet : DoElab := fun stx dec => do
  let `(doLet| let $[mut%$mutTk?]? $decl:letDecl) := stx | throwUnsupportedSyntax
  elabDoLetOrReassign (.let mutTk?) decl dec

@[builtin_doElem_elab Lean.Parser.Term.doHave] def elabDoHave : DoElab := fun stx dec => do
  let `(doHave| have $decl:letDecl) := stx | throwUnsupportedSyntax
  elabDoLetOrReassign .have decl dec

@[builtin_doElem_elab Lean.Parser.Term.doLetRec] def elabDoLetRec : DoElab := fun stx dec => do
  let `(doLetRec| let rec $decls:letRecDecls) := stx | throwUnsupportedSyntax
  let vars ← getLetRecDeclsVars decls
  let mγ ← mkMonadicType (← read).doBlockResultType
  doElabToSyntax m!"let rec body of group {vars}" dec.continueWithUnit fun body => do
    Term.elabTerm (← `(let rec $decls:letRecDecls; $body)) mγ (catchExPostpone := false)

@[builtin_doElem_elab Lean.Parser.Term.doReassign] def elabDoReassign : DoElab := fun stx dec => do
  -- def doReassign := letIdDeclNoBinders <|> letPatDecl
  -- And `letIdDeclNoBinders` is a `letIdDecl`. We wrap a `letDecl` node manually.
  let decl : TSyntax ``letDecl := ⟨mkNode ``letDecl #[stx.raw[0]]⟩
  elabDoLetOrReassign .reassign decl dec

@[builtin_doElem_elab Lean.Parser.Term.doLetElse] def elabDoLetElse : DoElab := fun stx dec => do
  let `(doLetElse| let $[mut%$mutTk?]? $pattern := $rhs | $otherwise:doSeq $body:doSeq) := stx | throwUnsupportedSyntax
  elabDoLetOrReassignElse (.let mutTk?) pattern rhs body otherwise dec

@[builtin_doElem_elab Lean.Parser.Term.doReassignElse] def elabDoReassignElse : DoElab := fun stx dec => do
  let `(doReassignElse| $pattern := $rhs | $otherwise:doSeq $body:doSeq) := stx | throwUnsupportedSyntax
  elabDoLetOrReassignElse .reassign pattern rhs body otherwise dec

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
  let doElemToTerm doElem := doElabToSyntax m!"if branch {doElem}" (ref := doElem) (elabDoSeq doElem dec)
  let condsThens := #[(cond, thenSeq)] ++ Array.zip conds thenSeqs
  let rec loop (i : Nat) : DoElabM Expr := do
    if h : i < condsThens.size then
      let (cond, thenSeq) := condsThens[i]
      doElemToTerm thenSeq fun then_ => do
      doElabToSyntax m!"else branch of {cond}" (loop (i + 1)) fun else_ => do
      match cond with
      | `(doIfCond|$cond) =>
        Term.elabTerm (← `(if $cond then $then_ else $else_)) mγ (catchExPostpone := false)
      | `(doIfCond|_ : $cond) =>
        Term.elabTerm (← `(if _ : $cond then $then_ else $else_)) mγ (catchExPostpone := false)
      | `(doIfCond|$h:ident : $cond) =>
        Term.elabTerm (← `(if $h:ident : $cond then $then_ else $else_)) mγ (catchExPostpone := false)
      | `(doIfCond|let $pat := $d) =>
        checkMutVarsForShadowing (← getPatternVarsEx pat)
        Term.elabTerm (← `(match $d:term with | $pat => $then_ | _ => $else_)) mγ (catchExPostpone := false)
      | `(doIfCond|let $pat ← $rhs) =>
        checkMutVarsForShadowing (← getPatternVarsEx pat)
        let x ← Term.mkFreshIdent pat
        elabDoIdDecl x none (← `(doElem| $rhs:term)) (contRef := pat) (declKind := .implDetail) do
          Term.elabTerm (← `(match $x:term with | $pat => $then_ | _ => $else_)) mγ (catchExPostpone := false)
      | _ => throwUnsupportedSyntax
    else
      match elseSeq? with
      | some elseSeq => elabDoSeq elseSeq dec
      | none         => dec.continueWithUnit
  loop 0

@[builtin_doElem_elab Lean.Parser.Term.doMatch] def elabDoMatch : DoElab := fun stx dec => do
  let `(doMatch| match $[$gen]? $[$motive]? $discrs,* with $alts:matchAlt*) := stx | throwUnsupportedSyntax
  -- We push the `DoElemCont` into each `match` alternative, altering its result type.
  -- We *could* try and propagate the `motive` to `dec.resultType`, but that seems complicated.
  if let `(generalizingParam| (generalizing := true)) := gen.getD ⟨.missing⟩ then
    throwErrorAt gen.get! "Match generalization is not supported by `do` syntax. Try to express your match as a term match."
  if let some motive := motive then
    -- We push the `DoElemCont` into each `match` alternative, altering its result type.
    -- We *could* try and propagate the `motive` to `dec.resultType`, but that seems complicated.
    throwErrorAt motive "Specifying a `match` motive is not supported in `do` blocks. Try to express your match as a term match."
  -- cf. `expandMatchAlts?`
  let alts : Array (TSyntax ``Term.matchAlt) :=
    if alts.any Term.shouldExpandMatchAlt then
      alts.foldl (init := #[]) fun alts alt =>
        alts ++ (Term.expandMatchAlt alt)
    else
      alts
  let mγ ← mkMonadicType (← read).doBlockResultType
  dec.withDuplicableCont fun dec => do
    let rec elabMatch i (alts : Array (TSyntax ``Term.matchAlt)) := do
      if h : i < alts.size then
        match alts[i] with
        | `(matchAltExpr| | $patterns,* => $seq) =>
          let vars ← getPatternsVarsEx patterns
          checkMutVarsForShadowing vars
          doElabToSyntax m!"match alternative {patterns.getElems}" (ref := seq) (elabDoSeq ⟨seq⟩ dec) fun rhs => do
            elabMatch (i + 1) (alts.set i (← `(matchAltExpr| | $patterns,* => $rhs)))
        | _ => throwUnsupportedSyntax
      else
        let mut motive : Term ← Term.exprToSyntax mγ
        for discr in discrs.getElems do
          motive ← `(∀ _, $motive)
        Term.elabTerm (← `(match (generalizing := false) (motive := $motive) $discrs,* with $alts:matchAlt*)) mγ (catchExPostpone := false)
    elabMatch 0 alts

@[builtin_doElem_elab Lean.Parser.Term.doMatchExpr] def elabDoMatchExpr : DoElab := fun stx dec => do
  let `(doMatchExpr| match_expr $[(meta := false)%$metaFalseTk?]? $discr:term with $alts) := stx | throwUnsupportedSyntax
  if metaFalseTk?.isNone then -- i.e., implicitly (meta := true)
    let x ← Term.mkFreshIdent discr
    elabDoIdDecl x none (← `(doElem| instantiateMVars $discr)) (contRef := dec.ref) (declKind := .implDetail) do
      elabDoMatchExprNoMeta x alts dec
  else
    elabDoMatchExprNoMeta discr alts dec
where elabDoMatchExprNoMeta (discr : Term) (alts : TSyntax ``Term.matchExprAlts) (dec : DoElemCont) : DoElabM Expr := do
  dec.withDuplicableCont fun dec => do
    let rec elabMatch i (altsArr : Array (TSyntax ``Term.matchExprAlt)) := do
      if h : i < altsArr.size then
        match altsArr[i] with
        | `(matchExprAltExpr| | $pattern => $seq) =>
          let vars ← getExprPatternVarsEx pattern
          checkMutVarsForShadowing vars
          doElabToSyntax m!"match_expr alternative {pattern}" (ref := seq) (elabDoSeq ⟨seq⟩ dec) fun rhs => do
            elabMatch (i + 1) (altsArr.set i (← `(matchExprAltExpr| | $pattern => $rhs)))
        | _ => throwUnsupportedSyntax
      else
        trace[Elab.do] "elseSeq: {repr alts.raw[1][3]}"
        let elseSeq := alts.raw[1][3]
        doElabToSyntax m!"match_expr else alternative" (ref := elseSeq) (elabDoSeq ⟨elseSeq⟩ dec) fun rhs => do
          let alts : TSyntax ``Term.matchExprAlts := ⟨alts.raw.modifyArg 0 fun node => node.setArgs altsArr⟩
          let alts : TSyntax ``Term.matchExprAlts := ⟨alts.raw.modifyArg 1 (·.setArg 3 rhs)⟩
          let mγ ← mkMonadicType (← read).doBlockResultType
          Term.elabTerm (← `(match_expr $discr with $alts)) mγ (catchExPostpone := false)
    elabMatch 0 (alts.raw[0].getArgs.map (⟨·⟩))

@[builtin_doElem_elab Lean.Parser.Term.doLetExpr] def elabDoLetExpr : DoElab := fun stx dec => do
  let `(doLetExpr| let_expr $pattern:matchExprPat := $rhs:term | $otherwise $body:doSeq) := stx | throwUnsupportedSyntax
  let γ := (← read).doBlockResultType
  let mγ ← mkMonadicType γ
  let otherwise ← elabDoSeq otherwise (← DoElemCont.mkPure γ)
  let otherwise ← Term.exprToSyntax otherwise
  let vars ← getExprPatternVarsEx pattern
  checkMutVarsForShadowing vars
  doElabToSyntax m!"let_expr body of {pattern}" (elabDoSeq body dec) (ref := dec.ref) fun body => do
    Term.elabTerm (← `(match_expr $rhs with | $pattern => $body | _ => $otherwise)) mγ (catchExPostpone := false)

@[builtin_doElem_elab Lean.Parser.Term.doLetMetaExpr] def elabDoLetMetaExpr : DoElab := fun stx dec => do
  let `(doLetMetaExpr| let_expr $pattern:matchExprPat ← $rhs:term | $otherwise $body:doSeq) := stx | throwUnsupportedSyntax
  let x ← Term.mkFreshIdent pattern
  elabDoIdDecl x none (← `(doElem| instantiateMVars $rhs)) (contRef := dec.ref) (declKind := .implDetail) do
    elabDoLetExpr (← `(doElem| let_expr $pattern:matchExprPat := $x | $otherwise $body:doSeq)) dec

@[builtin_doElem_elab Lean.Parser.Term.doUnless] def elabDoUnless : DoElab := fun stx dec => do
  let `(doUnless| unless $cond do $body) := stx | throwUnsupportedSyntax
  elabDoIf (← `(doElem| if $cond then pure PUnit.unit else $body)) dec

@[builtin_doElem_elab Lean.Parser.Term.doDbgTrace] def elabDoDbgTrace : DoElab := fun stx dec => do
  let `(doDbgTrace| dbg_trace $msg:term) := stx | throwUnsupportedSyntax
  let mγ ← mkMonadicType (← read).doBlockResultType
  let body ← dec.continueWithUnit
  let body ← Term.exprToSyntax body
  Term.elabTerm (← `(dbg_trace $msg; $body)) mγ (catchExPostpone := false)

@[builtin_doElem_elab Lean.Parser.Term.doAssert] def elabDoAssert : DoElab := fun stx dec => do
  let `(doAssert| assert! $cond) := stx | throwUnsupportedSyntax
  let mγ ← mkMonadicType (← read).doBlockResultType
  let body ← dec.continueWithUnit
  let body ← Term.exprToSyntax body
  Term.elabTerm (← `(assert! $cond; $body)) mγ (catchExPostpone := false)

@[builtin_doElem_elab Lean.Parser.Term.doDebugAssert] def elabDoDebugAssert : DoElab := fun stx dec => do
  let `(doDebugAssert| debug_assert! $cond) := stx | throwUnsupportedSyntax
  let mγ ← mkMonadicType (← read).doBlockResultType
  let body ← dec.continueWithUnit
  let body ← Term.exprToSyntax body
  Term.elabTerm (← `(debug_assert! $cond; $body)) mγ (catchExPostpone := false)

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
      let s := mkIdentFrom ys (← withFreshMacroScope <| MonadQuotation.addMacroScope `s)
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
  checkMutVarsForShadowing #[x]
  let uα ← mkFreshLevelMVar
  let uρ ← mkFreshLevelMVar
  let α ← mkFreshExprMVar (mkSort (mkLevelSucc uα)) (userName := `α) -- assigned by outParam
  let ρ ← mkFreshExprMVar (mkSort (mkLevelSucc uρ)) (userName := `ρ) -- assigned in the next line
  let xs ← Term.elabTermEnsuringType xs ρ
  let mi := (← read).monadInfo
  let σ ← mkFreshExprMVar (mkSort (mkLevelSucc mi.u)) (userName := `σ) -- assigned below
  let γ := (← read).doBlockResultType
  let β ← mkArrow σ (← mkMonadicType γ)
  let mutVars := (← read).mutVars
  let mutVarNames := mutVars.map (·.getId)
  let breakRhs ← mkFreshExprMVar β -- assigned below
  let (app, p?) ← match h? with
    | none =>
      let instForIn ← Term.mkInstMVar <| mkApp3 (mkConst ``ForInNew [uρ, uα, mi.u, mi.v]) mi.m ρ α
      let app := mkConst ``ForInNew.forInNew [uρ, uα, mi.u, mi.v]
      let app := mkApp7 app mi.m ρ α instForIn σ γ xs -- 3 args remaining: preS, kcons, knil
      pure (app, none)
    | some _ =>
      let p ← mkFreshExprMVar (← mkArrowN #[ρ, α] (mkSort .zero)) (userName := `p) -- outParam
      let instForIn ← Term.mkInstMVar <| mkApp4 (mkConst ``ForInNew' [uρ, uα, mi.u, mi.v]) mi.m ρ α p
      let app := mkConst ``ForInNew'.forInNew' [uρ, uα, mi.u, mi.v]
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
    let continueKVar ← mkFreshContVar γ (mutVarNames.push dec.resultName)
    let breakKVar ← mkFreshContVar γ mutVarNames

    -- Elaborate the loop body, which must have result type `PUnit`.
    -- The `withSynthesizeForDo` is so that we see all jump sites before continuing elaboration.
    let body ← withSynthesizeForDo <| enterLoopBody breakKVar.mkJump continueKVar.mkJump do
      elabDoSeq body { dec with k := continueKVar.mkJump, kind := .duplicable }

    -- Compute the set of mut vars that were reassigned on the path to a back jump (`continue`).
    -- Take care to preserve the declaration order that is manifest in the array `mutVars`.
    let loopMutVars ← do
      let ctn ← continueKVar.getReassignedMutVars rootCtx
      let brk ← breakKVar.getReassignedMutVars rootCtx
      pure (ctn.union brk)
    let loopMutVars := mutVars.filter (loopMutVars.contains ·.getId)
    let loopMutVarNames := loopMutVars.map (·.getId) |>.toList

    let useLoopMutVars : TermElabM (Array Expr) := do
      let mut defs := #[]
      for x in loopMutVars do
        let defn ← getFVarFromUserName x.getId
        Term.addTermInfo' x defn
        defs := defs.push defn
      return defs

    -- Assign the state tuple type and the initial tuple of states.
    let preS ← σ.mvarId!.withContext do
      let (tuple, tupleTy) ← mkProdMkN (← useLoopMutVars)
      synthUsingDefEq "state tuple type" σ tupleTy
      discard <| Term.ensureHasType (mkSort (mkLevelSucc mi.u)) σ
      pure tuple

    -- Synthesize the `continue` and `break` jumps.
    continueKVar.synthesizeJumps do
      let (tuple, _tupleTy) ← mkProdMkN (← useLoopMutVars)
      discard <| Term.ensureHasType σ tuple -- instantiate `?u` in `PUnit.unit.{?u}`
      return mkApp kcontinue tuple
    breakKVar.synthesizeJumps do
      let (tuple, _tupleTy) ← mkProdMkN (← useLoopMutVars)
      discard <| Term.ensureHasType σ tuple -- instantiate `?u` in `PUnit.unit.{?u}`
      return mkApp kbreak tuple

    -- Elaborate the continuation, now that `σ` is known. It will be the `break` handler.
    -- If there is a `break`, the code will be shared in the `kbreak` join point.
    breakRhs.mvarId!.withContext do
      let e ← withLocalDeclD (← mkFreshUserName `s) σ fun postS => do mkLambdaFVars #[postS] <| ← do
        bindMutVarsFromTuple loopMutVarNames postS.fvarId! do
          unless ← isDefEq dec.resultType (← mkPUnit) do
            throwError m!"Type mismatch. `for` loops have result type {← mkPUnit}, but the rest of the `do` sequence expected {dec.resultType}."
          dec.continueWithUnit
      synthUsingDefEq "break RHS" breakRhs e

    -- Finally eliminate the proxy variables from the loop body.
    -- * Point non-reassigned mut var defs to the pre state
    -- * Point the initial defs of reassigned mut vars to the loop state
    -- Done by `elimProxyDefs` below.
    let body ← bindMutVarsFromTuple loopMutVarNames loopS.fvarId! do
      elimProxyDefs body

    let needBreakJoin := (← breakKVar.jumpCount) > 0 && dec.kind matches .nonDuplicable
    let kcons ← mkLambdaFVars (xh ++ #[kcontinue, loopS]) body
    let knil := if needBreakJoin then kbreak else breakRhs
    let app := mkApp3 app preS kcons knil
    if needBreakJoin then
      mkLetFVars (generalizeNondepLet := false) #[kbreak] app
    else
      return (← elimMVarDeps #[kbreak] app).replaceFVar kbreak breakRhs

private def elabDoCatch (lifter : ControlLifter) (body : Expr) (catch_ : TSyntax ``doCatch) : DoElabM Expr := do
  let mi := (← read).monadInfo
  let `(doCatch| catch $x $[: $eType?]? => $catchSeq) := catch_ | throwUnsupportedSyntax
  let x := Term.mkExplicitBinder x <| match eType? with
    | some eType => eType
    | none => mkHole x
  let (catch_, ε, uε) ← controlAtTermElabM fun runInBase => do
    Term.elabBinder x fun x => runInBase do
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
    match catch_ with
    | `(doCatchMatch| catch $matchAlts) =>
      elabDoCatch lifter body (← `(doCatch| catch x => match x with $matchAlts))
    | `(doCatch| $catch_) =>
      elabDoCatch lifter body catch_
  let body ← match finSeq? with
    | none => pure body
    | some finSeq => do
      let β ← mkFreshResultType `β
      Term.registerMVarErrorHoleInfo β.mvarId! finSeq
      let fin ← enterFinally β <| elabDoSeq finSeq (← DoElemCont.mkPure β)
      let instMonadFinally ← Term.mkInstMVar <| mkApp (mkConst ``MonadFinally [mi.u, mi.v]) mi.m
      let instFunctor ← Term.mkInstMVar <| mkApp (mkConst ``Functor [mi.u, mi.v]) mi.m
      pure <| mkApp7 (mkConst ``tryFinally [mi.u, mi.v])
        mi.m lifter.resultType β instMonadFinally instFunctor body fin
  (← lifter.restoreCont).mkBindUnlessPure body
