/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
import Init.Grind.Util
import Init.Grind.Injective
import Init.Grind.PP
import Lean.Meta.Tactic.Grind.Arith.CommRing.PP
import Lean.Meta.Tactic.Grind.Arith.Linear.PP
import Lean.Meta.Tactic.Grind.AC.PP
import Lean.Meta.Tactic.Grind.CastLike
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Model
public section

namespace Lean.Meta.Grind

/-- Helper function for pretty printing the state for debugging purposes. -/
def Goal.ppENodeRef (goal : Goal) (e : Expr) : MetaM MessageData := do
  let some n := goal.getENode? e | return "_"
  let type ← inferType e
  let u ← getLevel type
  let d := mkApp3 (mkConst ``Grind.node_def [u]) (toExpr n.idx) type e
  return m!"{d}"

@[inherit_doc Goal.ppENodeRef]
def ppENodeRef (e : Expr) : GoalM MessageData := do
  (← get).ppENodeRef e

/-- Helper function for pretty printing the state for debugging purposes. -/
private def Goal.ppENodeDeclValue (goal : Goal) (e : Expr) : MetaM MessageData := do
  if e.isApp && !(← isLitValue e) then
    e.withApp fun f args => do
      let r ← if f.isConst then
        pure m!"{f}"
      else
        goal.ppENodeRef f
      let mut r := r
      for arg in args do
        r := r ++ " " ++ (← goal.ppENodeRef arg)
      return r
  else
    ppExpr e

/-- Helper function for pretty printing the state for debugging purposes. -/
private def Goal.ppENodeDecl (goal : Goal) (e : Expr) : MetaM MessageData := do
  let mut r := m!"{← goal.ppENodeRef e} := {← goal.ppENodeDeclValue e}"
  let n ← goal.getENode e
  unless isSameExpr e n.root do
    r := r ++ m!" ↦ {← goal.ppENodeRef n.root}"
  if n.interpreted then
    r := r ++ ", [val]"
  if n.ctor then
    r := r ++ ", [ctor]"
  if grind.debug.get (← getOptions) then
    if let some target := goal.getTarget? e then
      r := r ++ m!" ↝ {← goal.ppENodeRef target}"
  return r

/-- Pretty print goal state for debugging purposes. -/
def Goal.ppState (goal : Goal) : MetaM MessageData := do
  let mut r := m!"Goal:"
  for e in goal.exprs do
    let node ← goal.getENode e
    r := r ++ "\n" ++ (← goal.ppENodeDecl node.self)
  let eqcs := goal.getEqcs (sort := true)
  for eqc in eqcs do
    if eqc.length > 1 then
      r := r ++ "\n" ++ "{" ++ (MessageData.joinSep (← eqc.mapM goal.ppENodeRef) ", ") ++  "}"
  return r

def ppGoals (goals : List Goal) : MetaM MessageData := do
  let mut r := m!""
  for goal in goals do
    let m ← goal.ppState
    r := r ++ Format.line ++ m
  return r

private abbrev M := ReaderT Goal (StateT (Array MessageData) MetaM)

private def pushMsg (m : MessageData) : M Unit :=
  modify fun s => s.push m

def ppExprArray (cls : Name) (header : String) (es : Array Expr) (clsElem : Name := Name.mkSimple "_") (collapsed : Bool := true) : MessageData :=
  let es := es.map (toTraceElem · clsElem)
  .trace { cls, collapsed } header es

section EqcFilter
/-!
Functions for deciding whether an expression is a support application or not
when displaying equivalence classes.
This is hard-coded for now. We will probably make it extensible in the future.
-/
private def isGadget (declName : Name) : Bool :=
  declName == ``Grind.nestedDecidable || declName == ``Grind.leftInv

private def isBuiltin (declName : Name) : Bool :=
  declName == ``ite || declName == ``dite || declName == ``cast

/-- Result for helper function `isArithOfCastLike` -/
private inductive Result where
  | num | cast | no
  deriving Inhabited

@[macro_inline] private def Result.and : Result → Result → Result
  | .no,   _ | _, .no   => .no
  | .cast, _ | _, .cast => .cast
  | .num, .num => .num

/--
Returns `true` if `e` is an expression constructed using numerals,
`grind` cast-like operations, and arithmetic terms. Moreover, the
expression contains at least one cast-like application.
This kind of term is constructed by `grind` satellite solvers.
-/
private partial def isArithOfCastLike (e : Expr) : Bool :=
  go e matches .cast
where
  go (e : Expr) : Result :=
    match_expr e with
    | HAdd.hAdd _ _ _ _ a b => go a |>.and (go b)
    | HSub.hSub _ _ _ _ a b => go a |>.and (go b)
    | HMul.hMul _ _ _ _ a b => go a |>.and (go b)
    | HDiv.hDiv _ _ _ _ a b => go a |>.and (go b)
    | HMod.hMod _ _ _ _ a b => go a |>.and (go b)
    | HPow.hPow _ _ _ _ a _ => go a
    | Neg.neg _ _ a         => go a
    | OfNat.ofNat _ _ _     => .num
    | _ => if isCastLikeApp e then .cast else .no

/--
Returns `true` if `e` is a support-like application.
Recall that equivalence classes that contain only support applications are displayed in the "others" category.
-/
def isSupportApp (e : Expr) : MetaM Bool := do
  if isArithOfCastLike e then return true
  let .const declName _ := e.getAppFn | return false
  -- Check whether `e` is the projection of a constructor
  if let some info ← getProjectionFnInfo? declName then
    if e.getAppNumArgs == info.numParams + 1 then
      if (← isConstructorApp e.appArg!) then
        return true
  return isCastLikeDeclName declName || isGadget declName || isBuiltin declName || isMatcherCore (← getEnv) declName

end EqcFilter

def ppEqc (eqc : List Expr) (children : Array MessageData := #[]) : MessageData :=
  .trace { cls := `eqc } (.group ("{" ++ (MessageData.joinSep (eqc.map toMessageData) ("," ++ Format.line)) ++  "}")) children

private def ppEqcs (collapsedProps := true) : M Unit := do
   let mut trueEqc?  : Option MessageData := none
   let mut falseEqc? : Option MessageData := none
   let mut regularEqcs : Array MessageData := #[]
   let mut otherEqcs : Array MessageData := #[]
   let goal ← read
   for eqc in goal.getEqcs (sort := true) do
     if Option.isSome <| eqc.find? (·.isTrue) then
       let eqc := eqc.filter fun e => !e.isTrue
       unless eqc.isEmpty do
         trueEqc? := ppExprArray `eqc  "True propositions" eqc.toArray `prop (collapsed := collapsedProps)
     else if Option.isSome <| eqc.find? (·.isFalse) then
       let eqc := eqc.filter fun e => !e.isFalse
       unless eqc.isEmpty do
         falseEqc? := ppExprArray `eqc "False propositions" eqc.toArray `prop (collapsed := collapsedProps)
     else if let e :: _ :: _ := eqc then
       -- We may want to add a flag to pretty print equivalence classes of nested proofs
       unless (← isProof e) do
         let mainEqc ← eqc.filterM fun e => return !(← isSupportApp e)
         if mainEqc.length <= 1 then
           otherEqcs := otherEqcs.push <| ppEqc eqc
         else
           let supportEqc ← eqc.filterM fun e => isSupportApp e
           if supportEqc.isEmpty then
             regularEqcs := regularEqcs.push <| ppEqc mainEqc
           else
             regularEqcs := regularEqcs.push <| ppEqc mainEqc #[ppEqc supportEqc]

   unless otherEqcs.isEmpty do
     regularEqcs := regularEqcs.push <| .trace { cls := `eqc } "others" otherEqcs
   if let some trueEqc := trueEqc? then pushMsg trueEqc
   if let some falseEqc := falseEqc? then pushMsg falseEqc
   unless regularEqcs.isEmpty do
     pushMsg <| .trace { cls := `eqc } "Equivalence classes" regularEqcs

private def ppEMatchTheorem (thm : EMatchTheorem) : MetaM MessageData := do
  let m := m!"{thm.origin.pp}: {thm.patterns.map ppPattern}"
  return .trace { cls := `thm } m #[]

private def ppActiveTheoremPatterns : M Unit := do
  let goal ← read
  let m ← goal.ematch.thms.toArray.mapM fun thm => ppEMatchTheorem thm
  let m := m ++ (← goal.ematch.newThms.toArray.mapM fun thm => ppEMatchTheorem thm)
  unless m.isEmpty do
    pushMsg <| .trace { cls := `ematch } "E-matching patterns" m

def Arith.Cutsat.pp? (goal : Goal) : MetaM (Option MessageData) := do
  let s ← Arith.Cutsat.cutsatExt.getStateCore goal
  let nodes := s.varMap
  if nodes.isEmpty then return none
  let model ← Arith.Cutsat.mkModel goal
  if model.isEmpty then return none
  let mut ms := #[]
  for (e, val) in model do
    ms := ms.push <| .trace { cls := `assign } m!"{Arith.quoteIfArithTerm e} := {val}" #[]
  return some <| .trace { cls := `cutsat } "Assignment satisfying linear constraints" ms

private def ppCutsat : M Unit := do
  let some msg ← Arith.Cutsat.pp? (← read) | return ()
  pushMsg msg

private def ppCommRing : M Unit := do
  let some msg ← Arith.CommRing.pp? (← read) | return ()
  pushMsg msg

private def ppLinarith : M Unit := do
  let some msg ← Arith.Linear.pp? (← read) | return ()
  pushMsg msg

private def ppAC : M Unit := do
  let some msg ← AC.pp? (← read) | return ()
  pushMsg msg

private def ppThresholds (c : Grind.Config) : M Unit := do
  let goal ← read
  let maxGen := goal.exprs.foldl (init := 0) fun g e =>
    if let some n := goal.getENode? e then
      Nat.max g n.generation
    else
      g
  let mut msgs := #[]
  if goal.ematch.numInstances ≥ c.instances  then
    msgs := msgs.push <| .trace { cls := `limit } m!"maximum number of instances generated by E-matching has been reached, threshold: `(instances := {c.instances})`" #[]
  if goal.ematch.num ≥ c.ematch  then
    msgs := msgs.push <| .trace { cls := `limit } m!"maximum number of E-matching rounds has been reached, threshold: `(ematch := {c.ematch})`" #[]
  if goal.split.num ≥ c.splits then
    msgs := msgs.push <| .trace { cls := `limit } m!"maximum number of case-splits has been reached, threshold: `(splits := {c.splits})`" #[]
  if maxGen ≥ c.gen then
    msgs := msgs.push <| .trace { cls := `limit } m!"maximum term generation has been reached, threshold: `(gen := {c.gen})`" #[]
  msgs ← Arith.CommRing.addThresholdMessage goal c msgs
  unless msgs.isEmpty do
    pushMsg <| .trace { cls := `limits } "Thresholds reached" msgs

private def ppCasesTrace : M Unit := do
  let goal ← read
  unless goal.split.trace.isEmpty do
    let mut msgs := #[]
    for { expr, i , num, source } in goal.split.trace.reverse do
      msgs := msgs.push <| .trace { cls := `cases } m!"[{i+1}/{num}]: {expr}" #[
        .trace { cls := `cases } m!"source: {source.toMessageData}" #[]
      ]
    pushMsg <| .trace { cls := `cases } "Case analyses" msgs

def goalDiagToMessageData (goal : Goal) (config : Grind.Config) (header := "Goal diagnostics") (collapsedMain := true)
     : MetaM MessageData := do
  let (_, m) ← go goal |>.run #[]
  let gm := MessageData.trace { cls := `grind, collapsed := false } header m
  return gm
where
  go : M Unit := do
    pushMsg <| ppExprArray `facts "Asserted facts" goal.facts.toArray `prop (collapsed := collapsedMain)
    ppEqcs (collapsedProps := collapsedMain)
    ppCasesTrace
    ppActiveTheoremPatterns
    ppCutsat
    ppLinarith
    ppCommRing
    ppAC
    ppThresholds config

def goalToMessageData (goal : Goal) (config : Grind.Config) : MetaM MessageData := goal.withContext do
  if config.verbose then
    let gm ← goalDiagToMessageData goal config
    let r := m!"{.ofGoal goal.mvarId}\n{gm}"
    addMessageContextFull r
  else
    return .ofGoal goal.mvarId

end Lean.Meta.Grind
