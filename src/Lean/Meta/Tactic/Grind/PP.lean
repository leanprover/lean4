/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Util
import Init.Grind.PP
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Arith.Model

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
  let nodes := goal.getENodes
  for node in nodes do
    r := r ++ "\n" ++ (← goal.ppENodeDecl node.self)
  let eqcs := goal.getEqcs
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

private def ppExprArray (cls : Name) (header : String) (es : Array Expr) (clsElem : Name := Name.mkSimple "_") : MessageData :=
  let es := es.map fun e => .trace { cls := clsElem} m!"{e}" #[]
  .trace { cls } header es

private abbrev M := ReaderT Goal (StateT (Array MessageData) MetaM)

private def pushMsg (m : MessageData) : M Unit :=
  modify fun s => s.push m

private def ppEqcs : M Unit := do
   let mut trueEqc?  : Option MessageData := none
   let mut falseEqc? : Option MessageData := none
   let mut otherEqcs : Array MessageData := #[]
   let goal ← read
   for eqc in goal.getEqcs do
     if Option.isSome <| eqc.find? (·.isTrue) then
       let eqc := eqc.filter fun e => !e.isTrue
       unless eqc.isEmpty do
         trueEqc? := ppExprArray `eqc "True propositions" eqc.toArray `prop
     else if Option.isSome <| eqc.find? (·.isFalse) then
       let eqc := eqc.filter fun e => !e.isFalse
       unless eqc.isEmpty do
         falseEqc? := ppExprArray `eqc "False propositions" eqc.toArray `prop
     else if let e :: _ :: _ := eqc then
       -- We may want to add a flag to pretty print equivalence classes of nested proofs
       unless (← isProof e) do
         otherEqcs := otherEqcs.push <| .trace { cls := `eqc } (.group ("{" ++ (MessageData.joinSep (eqc.map toMessageData) ("," ++ Format.line)) ++  "}")) #[]
   if let some trueEqc := trueEqc? then pushMsg trueEqc
   if let some falseEqc := falseEqc? then pushMsg falseEqc
   unless otherEqcs.isEmpty do
     pushMsg <| .trace { cls := `eqc } "Equivalence classes" otherEqcs

private def ppEMatchTheorem (thm : EMatchTheorem) : MetaM MessageData := do
  let m := m!"{← thm.origin.pp}: {thm.patterns.map ppPattern}"
  return .trace { cls := `thm } m #[]

private def ppActiveTheoremPatterns : M Unit := do
  let goal ← read
  let m ← goal.ematch.thms.toArray.mapM fun thm => ppEMatchTheorem thm
  let m := m ++ (← goal.ematch.newThms.toArray.mapM fun thm => ppEMatchTheorem thm)
  unless m.isEmpty do
    pushMsg <| .trace { cls := `ematch } "E-matching patterns" m

private def ppOffset : M Unit := do
  let goal ← read
  let s := goal.arith.offset
  let nodes := s.nodes
  if nodes.isEmpty then return ()
  let model ← Arith.Offset.mkModel goal
  if model.isEmpty then return ()
  let mut ms := #[]
  for (e, val) in model do
    ms := ms.push <| .trace { cls := `assign } m!"{quoteIfNotAtom e} := {val}" #[]
  pushMsg <| .trace { cls := `offset } "Assignment satisfying offset contraints" ms

private def ppCutsat : M Unit := do
  let goal ← read
  let s := goal.arith.cutsat
  let nodes := s.varMap
  if nodes.isEmpty then return ()
  let model ← Arith.Cutsat.mkModel goal
  if model.isEmpty then return ()
  let mut ms := #[]
  for (e, val) in model do
    ms := ms.push <| .trace { cls := `assign } m!"{quoteIfNotAtom e} := {val}" #[]
  pushMsg <| .trace { cls := `cutsat } "Assignment satisfying integer contraints" ms

private def ppThresholds (c : Grind.Config) : M Unit := do
  let goal ← read
  let maxGen := goal.enodes.foldl (init := 0) fun g _ n => Nat.max g n.generation
  let mut msgs := #[]
  if goal.ematch.numInstances ≥ c.instances  then
    msgs := msgs.push <| .trace { cls := `limit } m!"maximum number of instances generated by E-matching has been reached, threshold: `(instances := {c.instances})`" #[]
  if goal.ematch.num ≥ c.ematch  then
    msgs := msgs.push <| .trace { cls := `limit } m!"maximum number of E-matching rounds has been reached, threshold: `(ematch := {c.ematch})`" #[]
  if goal.split.num ≥ c.splits then
    msgs := msgs.push <| .trace { cls := `limit } m!"maximum number of case-splits has been reached, threshold: `(splits := {c.splits})`" #[]
  if maxGen ≥ c.gen then
    msgs := msgs.push <| .trace { cls := `limit } m!"maximum term generation has been reached, threshold: `(gen := {c.gen})`" #[]
  unless msgs.isEmpty do
    pushMsg <| .trace { cls := `limits } "Thresholds reached" msgs

private def ppCasesTrace : M Unit := do
  let goal ← read
  unless goal.split.trace.isEmpty do
    let mut msgs := #[]
    for { expr, i , num } in goal.split.trace.reverse do
      msgs := msgs.push <| .trace { cls := `cases } m!"[{i+1}/{num}]: {expr}" #[]
    pushMsg <| .trace { cls := `cases } "Case analyses" msgs

def goalToMessageData (goal : Goal) (config : Grind.Config) : MetaM MessageData := goal.mvarId.withContext do
  if config.verbose then
    let (_, m) ← go goal |>.run #[]
    let gm := MessageData.trace { cls := `grind, collapsed := false } "Goal diagnostics" m
    let r := m!"{.ofGoal goal.mvarId}\n{gm}"
    addMessageContextFull r
  else
    return .ofGoal goal.mvarId
where
  go : M Unit := do
    pushMsg <| ppExprArray `facts "Asserted facts" goal.facts.toArray `prop
    ppEqcs
    ppCasesTrace
    ppActiveTheoremPatterns
    ppOffset
    ppCutsat
    ppThresholds config

end Lean.Meta.Grind
