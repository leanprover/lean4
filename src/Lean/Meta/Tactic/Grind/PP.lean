/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Util
import Lean.Meta.Tactic.Grind.Types

namespace Lean.Meta.Grind

/-- Helper function for pretty printing the state for debugging purposes. -/
def ppENodeRef (e : Expr) : GoalM Format := do
  let some n ← getENode? e | return "_"
  return f!"#{n.idx}"

/-- Returns expressions in the given expression equivalence class. -/
partial def getEqc (e : Expr) : GoalM (List Expr) :=
  go e e []
where
  go (first : Expr) (e : Expr) (acc : List Expr) : GoalM (List Expr) := do
    let next ← getNext e
    let acc := e :: acc
    if isSameExpr first next then
      return acc
    else
      go first next acc

/-- Returns all equivalence classes in the current goal. -/
partial def getEqcs : GoalM (List (List Expr)) := do
  let mut r := []
  let nodes ← getENodes
  for node in nodes do
    if isSameExpr node.root node.self then
      r := (← getEqc node.self) :: r
  return r

/-- Helper function for pretty printing the state for debugging purposes. -/
def ppENodeDeclValue (e : Expr) : GoalM Format := do
  if e.isApp && !(← isLitValue e) then
    e.withApp fun f args => do
      let r ← if f.isConst then
        ppExpr f
      else
        ppENodeRef f
      let mut r := r
      for arg in args do
        r := r ++ " " ++ (← ppENodeRef arg)
      return r
  else
    ppExpr e

/-- Helper function for pretty printing the state for debugging purposes. -/
def ppENodeDecl (e : Expr) : GoalM Format := do
  let mut r := f!"{← ppENodeRef e} := {← ppENodeDeclValue e}"
  let n ← getENode e
  unless isSameExpr e n.root do
    r := r ++ f!" ↦ {← ppENodeRef n.root}"
  if n.interpreted then
    r := r ++ ", [val]"
  if n.ctor then
    r := r ++ ", [ctor]"
  if grind.debug.get (← getOptions) then
    if let some target ← getTarget? e then
      r := r ++ f!" ↝ {← ppENodeRef target}"
  return r

/-- Pretty print goal state for debugging purposes. -/
def ppState : GoalM Format := do
  let mut r := f!"Goal:"
  let nodes ← getENodes
  for node in nodes do
    r := r ++ "\n" ++ (← ppENodeDecl node.self)
  let eqcs ← getEqcs
  for eqc in eqcs do
    if eqc.length > 1 then
      r := r ++ "\n" ++ "{" ++ (Format.joinSep (← eqc.mapM ppENodeRef) ", ") ++  "}"
  return r

end Lean.Meta.Grind
