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

private def ppEqcs (goal : Goal) : MetaM (Array MessageData) := do
   let mut trueEqc?  : Option MessageData := none
   let mut falseEqc? : Option MessageData := none
   let mut otherEqcs : Array MessageData := #[]
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
   let mut result := #[]
   if let some trueEqc := trueEqc? then result := result.push trueEqc
   if let some falseEqc := falseEqc? then result := result.push falseEqc
   unless otherEqcs.isEmpty do
     result := result.push <| .trace { cls := `eqc } "Equivalence classes" otherEqcs
   return result

private def ppEMatchTheorem (thm : EMatchTheorem) : MetaM MessageData := do
  let m := m!"{← thm.origin.pp}\n{← inferType thm.proof}\npatterns: {thm.patterns.map ppPattern}"
  return .trace { cls := `thm } m #[]

private def ppActiveTheorems (goal : Goal) : MetaM MessageData := do
  let m ← goal.thms.toArray.mapM ppEMatchTheorem
  let m := m ++ (← goal.newThms.toArray.mapM ppEMatchTheorem)
  if m.isEmpty then
    return ""
  else
    return .trace { cls := `ematch } "E-matching" m

def ppOffset (goal : Goal) : MetaM MessageData := do
  let s := goal.arith.offset
  let nodes := s.nodes
  if nodes.isEmpty then return ""
  let model ← Arith.Offset.mkModel goal
  let mut ms := #[]
  for (e, val) in model do
    ms := ms.push <| .trace { cls := `assign } m!"{e} := {val}" #[]
  return .trace { cls := `offset } "Assignment satisfying offset contraints" ms

def goalToMessageData (goal : Goal) : MetaM MessageData := goal.mvarId.withContext do
  let mut m : Array MessageData := #[.ofGoal goal.mvarId]
  m := m.push <| ppExprArray `facts "Asserted facts" goal.facts.toArray `prop
  m := m ++ (← ppEqcs goal)
  m := m.push (← ppActiveTheorems goal)
  m := m.push (← ppOffset goal)
  addMessageContextFull <| MessageData.joinSep m.toList ""

def goalsToMessageData (goals : List Goal) : MetaM MessageData :=
  return MessageData.joinSep (← goals.mapM goalToMessageData) m!"\n"

end Lean.Meta.Grind
