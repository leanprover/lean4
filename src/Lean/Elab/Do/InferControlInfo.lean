/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Syntax
public import Lean.Parser
meta import Lean.Parser.Do

public section

namespace Lean.Elab.Do

open Lean Meta Parser.Term

structure ControlInfo where
  breaks : Bool := false
  continues : Bool := false
  returnsEarly : Bool := false
  exitsRegularly : Bool := true
  reassigns : NameSet := {}
  deriving Inhabited

def ControlInfo.pure : ControlInfo := {}

def ControlInfo.sequence (a b : ControlInfo) : ControlInfo :=
  if !a.exitsRegularly then a else {
    breaks := a.breaks || b.breaks,
    continues := a.continues || b.continues,
    returnsEarly := a.returnsEarly || b.returnsEarly,
    exitsRegularly := b.exitsRegularly,
    reassigns := a.reassigns ++ b.reassigns,
  }

def ControlInfo.alternative (a b : ControlInfo) : ControlInfo := {
    breaks := a.breaks || b.breaks,
    continues := a.continues || b.continues,
    returnsEarly := a.returnsEarly || b.returnsEarly,
    exitsRegularly := a.exitsRegularly || b.exitsRegularly,
    reassigns := a.reassigns ++ b.reassigns,
  }

instance : ToMessageData ControlInfo where
  toMessageData info := m!"breaks: {info.breaks}, continues: {info.continues},
    returnsEarly: {info.returnsEarly}, exitsRegularly: {info.exitsRegularly},
    reassigns: {info.reassigns.toList}"

private def getPatternVarsEx (pattern : Term) : TermElabM (Array Ident) :=
  open TSyntax.Compat in -- until PatternVar := Ident
  Term.getPatternVars pattern <|>
  Term.Quotation.getPatternVars pattern

private def getLetIdVars (letId : TSyntax ``letId) : TermElabM (Array Ident) := do
  match letId with
  | `(letId| _) => return #[]
  | `(letId| $id:ident) => return #[id]
  | `(letId| $s:hygieneInfo) => return #[HygieneInfo.mkIdent s `this (canonical := true)]
  | _ => throwError "Not a letId: {letId}"

private def getLetIdDeclVars (letIdDecl : TSyntax ``letIdDecl) : TermElabM (Array Ident) := do
  -- def letIdDecl := leading_parser letIdLhs >> " := " >> termParser
  -- def letIdLhs : Parser := letId >> many (ppSpace >> letIdBinder) >> optType
  -- NB: `letIdLhs` does not introduce a new node
  getLetIdVars ⟨letIdDecl.raw[0]⟩


private def getLetPatDeclVars (letPatDecl : TSyntax ``letPatDecl) : TermElabM (Array Ident) := do
  -- def letPatDecl := leading_parser termParser >> pushNone >> optType >> " := " >> termParser
  getPatternVarsEx ⟨letPatDecl.raw[0]⟩

private def getLetEqnsDeclVars (letEqnsDecl : TSyntax ``letEqnsDecl) : TermElabM (Array Ident) :=
  -- def letEqnsDecl := leading_parser letIdLhs >> matchAlts
  -- def letIdLhs : Parser := letId >> many (ppSpace >> letIdBinder) >> optType
  -- NB: `letIdLhs` does not introduce a new node
  getLetIdVars ⟨letEqnsDecl.raw[0]⟩

private def getLetDeclVars (letDecl : TSyntax ``letDecl) : TermElabM (Array Ident) := do
  match letDecl with
  | `(letDecl| $letIdDecl:letIdDecl) => getLetIdDeclVars letIdDecl
  | `(letDecl| $letPatDecl:letPatDecl) => getLetPatDeclVars ⟨letPatDecl⟩
  | `(letDecl| $letEqnsDecl:letEqnsDecl) => getLetEqnsDeclVars letEqnsDecl
  | _ => throwError "Not a let declaration: {toString letDecl}"

private def getDoLetDeclVars (letDecl : TSyntax [``doIdDecl, ``doPatDecl]) : TermElabM (Array Ident) := do
  match letDecl with
  | `(letDecl| $letIdDecl:letIdDecl) => getLetIdDeclVars letIdDecl
  | `(letDecl| $letPatDecl:letPatDecl) => getLetPatDeclVars ⟨letPatDecl⟩
  | `(letDecl| $letEqnsDecl:letEqnsDecl) => getLetEqnsDeclVars letEqnsDecl
  | _ => throwError "Not a let declaration: {toString letDecl}"

private def getLetRecDeclVars (letRecDecl : TSyntax ``letRecDecl) : TermElabM (Array Ident) := do
  -- def letRecDecl := optional docComment >> optional «attributes» >> letDecl >> Termination.suffix
  getLetDeclVars ⟨letRecDecl.raw[2]⟩

private def getLetRecDeclsVars (letRecDecls : TSyntax ``letRecDecls) : TermElabM (Array Ident) := do
  -- def letRecDecls := sepBy1 letRecDecl ", "
  let `(letRecDecls| $[$letRecDecls:letRecDecl],*) := letRecDecls | throwUnsupportedSyntax
  let mut allVars := #[]
  for letRecDecl in letRecDecls do
    let vars ← getLetRecDeclVars letRecDecl
    allVars := allVars ++ vars
  return allVars

namespace InferControlInfo

mutual

partial def ofElem (stx : TSyntax `doElem) : TermElabM ControlInfo := do
  let env ← getEnv
  if let some (_decl, stxNew?) ← liftMacroM (expandMacroImpl? env stx) then
    let stxNew ← liftMacroM <| liftExcept stxNew?
    return ← ofElem ⟨stxNew⟩

  match stx with
  | `(doElem| break) => return { breaks := true, exitsRegularly := false }
  | `(doElem| continue) => return { continues := true, exitsRegularly := false }
  | `(doElem| return $[$_]?) => return { returnsEarly := true, exitsRegularly := false }
  | `(doExpr| $_:term) => return { exitsRegularly := true }
  | `(doElem| do $doSeq) => ofSeq doSeq
  -- Let
  | `(doElem| let $[mut]? $_:letDecl) => return .pure
  | `(doElem| have $_:letDecl) => return .pure
  | `(doElem| let $[mut]? $_ := $_ | $otherwise $(body?)?) =>
    ofLetOrReassign #[] none otherwise body?
  | `(doElem| let $[mut]? $decl) =>
    ofLetOrReassignArrow false decl
  | `(doElem| $decl:letIdDeclNoBinders) =>
    ofLetOrReassign (← getLetIdDeclVars ⟨decl⟩) none none none
  | `(doElem| $decl:letPatDecl) =>
    ofLetOrReassign (← getLetPatDeclVars ⟨decl⟩) none none none
  | `(doElem| $decl:doIdDecl) =>
    ofLetOrReassignArrow true decl
  | `(doElem| $decl:doPatDecl) =>
    ofLetOrReassignArrow true decl
  -- match
  | `(doElem| match $[(generalizing := $_)]? $(_)? $_,* with $alts:matchAlt*) =>
    let mut info := {}
    for alt in alts do
      let `(matchAltExpr| | $[$_,*]|* => $rhs) := alt | throwUnsupportedSyntax
      let rhsInfo ← ofSeq ⟨rhs⟩
      info := info.alternative rhsInfo
    return info
  -- If
  | `(doElem| if $_:doIfCond then $thenSeq $[else if $_:doIfCond then $thenSeqs]* $[else $elseSeq?]?) =>
    let mut info ← ofOptionSeq elseSeq?
    -- Since doIfLetBind does not allow `doElem`, `cond` always has default `ControlInfo`.
    for thenSeq in thenSeqs.reverse do
      let thenInfo ← ofSeq thenSeq
      info := thenInfo.alternative info
    let thenInfo ← ofSeq thenSeq
    return thenInfo.alternative info
  | `(doElem| unless $_ do $elseSeq) =>
    ControlInfo.alternative {} <$> ofSeq elseSeq
  | `(doElem| for $[$[$_ :]? $_ in $_],* do $bodySeq) =>
    let info ← ofSeq bodySeq
    return { info with  -- keep only reassigns and earlyReturn
      exitsRegularly := true,
      continues := false,
      breaks := false
    }
  -- Try
  | `(doElem| try $trySeq:doSeq $[$catches]* $[finally $finSeq?]?) =>
    let mut info ← ofSeq trySeq
    for catch_ in catches do
      match catch_ with
      | `(doCatch| catch $_ $[: $_]? => $catchSeq) =>
        let catchInfo ← ofSeq catchSeq
        info := catchInfo.alternative info
      | `(doCatchMatch| catch $matchAlts:matchAlt*) =>
        for alt in matchAlts do
          let `(matchAltExpr| | $[$_,*]|* => $rhs) := alt | throwUnsupportedSyntax
          let catchInfo ← ofSeq ⟨rhs⟩
          info := info.alternative catchInfo
      | _ => throwError "Not a catch or catch match: {toString catch_}"
    let finInfo ← ofOptionSeq finSeq?
    return info.sequence finInfo
  -- Misc
  | `(doElem| dbg_trace $_) => return .pure
  | `(doElem| assert! $_) => return .pure
  | `(doElem| debug_assert! $_) => return .pure
  -- match_expr and let_expr
  | `(doElem| match_expr $[(meta := false)]? $_ with $[| $_:matchExprPat => $rhsSeqs]* | _ => $elseSeq) =>
    let mut info ← ofSeq elseSeq
    for rhsSeq in rhsSeqs do
      let rhsInfo ← ofSeq rhsSeq
      info := rhsInfo.alternative info
    return info
  | `(doElem| let_expr $_ := $_ | $otherwise $(body?)?)
  | `(doElem| let_expr $_ ← $_ | $otherwise $(body?)?) =>
    -- rhs is always just a term
    let otherwiseInfo ← ofSeq ⟨otherwise⟩
    let bodyInfo ← match body? with | none => pure {} | some body => ofSeq ⟨body⟩
    return otherwiseInfo.alternative bodyInfo
  | _ => throwError "unexpected `do` element syntax in `ofElem`: {indentD stx}"

partial def ofLetOrReassignArrow (reassignment : Bool) (decl : TSyntax [``doIdDecl, ``doPatDecl]) : TermElabM ControlInfo := do
  match decl with
  | `(doIdDecl| $x:ident $[: $_]? ← $rhs) =>
    let reassigns := if reassignment then #[x] else #[]
    ofLetOrReassign reassigns rhs none none
  | `(doPatDecl| $pattern ← $rhs $[| $otherwise? $[$body??]?]?) =>
    let reassigns ← if reassignment then getPatternVarsEx pattern else pure #[]
    ofLetOrReassign reassigns rhs otherwise? body??.join
  | _ => throwError "Not a let or reassignment declaration: {toString decl}"

partial def ofLetOrReassign (reassigned : Array Ident) (rhs? : Option (TSyntax `doElem))
    (otherwise? : Option (TSyntax ``doSeqIndent)) (body? : Option (TSyntax ``doSeqIndent))
    : TermElabM ControlInfo := do
  let rhs ← match rhs? with | none => pure { : ControlInfo } | some rhs => ofElem rhs
  let otherwise ← match otherwise? with | none => pure { : ControlInfo } | some otherwise => ofSeq ⟨otherwise⟩
  let body ← match body? with | none => pure { : ControlInfo } | some body => ofSeq ⟨body⟩
  let info := rhs.sequence (body.alternative otherwise)
  return { info with reassigns := (reassigned.map TSyntax.getId).foldl NameSet.insert info.reassigns }

partial def ofSeq (stx : TSyntax ``doSeq) : TermElabM ControlInfo := do
  let mut info : ControlInfo := {}
  for elem in getDoElems stx do
    if !info.exitsRegularly then
      break
    let elemInfo ← ofElem elem
    info := {
      info with
      breaks := info.breaks || elemInfo.breaks
      continues := info.continues || elemInfo.continues
      returnsEarly := info.returnsEarly || elemInfo.returnsEarly
      exitsRegularly := elemInfo.exitsRegularly
      reassigns := info.reassigns ++ elemInfo.reassigns
    }
  return info

partial def ofOptionSeq (stx? : Option (TSyntax ``doSeq)) : TermElabM ControlInfo := do
  match stx? with | none => pure { : ControlInfo } | some stx => ofSeq stx

end

end InferControlInfo

def inferControlInfoSeq (doSeq : TSyntax ``doSeq) : TermElabM ControlInfo :=
  InferControlInfo.ofSeq doSeq

def inferControlInfoElem (doElem : TSyntax `doElem) : TermElabM ControlInfo :=
  InferControlInfo.ofElem doElem
