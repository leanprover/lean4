/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Util
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Inv
import Lean.Meta.LitValues

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

/--
Returns `true` if `e` is `True`, `False`, or a literal value.
See `LitValues` for supported literals.
-/
def isInterpreted (e : Expr) : MetaM Bool := do
  if e.isTrue || e.isFalse then return true
  isLitValue e

/--
Creates an `ENode` for `e` if one does not already exist.
This method assumes `e` has been hashconsed.
-/
def mkENode (e : Expr) (generation : Nat) : GoalM Unit := do
  if (← alreadyInternalized e) then return ()
  let ctor := (← isConstructorAppCore? e).isSome
  let interpreted ← isInterpreted e
  mkENodeCore e interpreted ctor generation

private def pushNewEqCore (lhs rhs proof : Expr) (isHEq : Bool) : GoalM Unit :=
  modify fun s => { s with newEqs := s.newEqs.push { lhs, rhs, proof, isHEq } }

@[inline] private def pushNewEq (lhs rhs proof : Expr) : GoalM Unit := do
  if (← isDefEq (← inferType lhs) (← inferType rhs)) then
    pushNewEqCore lhs rhs proof (isHEq := false)
  else
    pushNewEqCore lhs rhs proof (isHEq := true)

/-- We use this auxiliary constant to mark delayed congruence proofs. -/
private def congrPlaceholderProof := mkConst (Name.mkSimple "[congruence]")

/-- Adds `e` to congruence table. -/
def addCongrTable (e : Expr) : GoalM Unit := do
  if let some { e := e' } := (← get).congrTable.find? { e } then
    trace[grind.congr] "{e} = {e'}"
    pushNewEq e e' congrPlaceholderProof
    -- TODO: we must check whether the types of the functions are the same
    -- TODO: update cgRoot for `e`
  else
    modify fun s => { s with congrTable := s.congrTable.insert { e } }

partial def internalize (e : Expr) (generation : Nat) : GoalM Unit := do
  if (← alreadyInternalized e) then return ()
  match e with
  | .bvar .. => unreachable!
  | .sort .. => return ()
  | .fvar .. | .letE .. | .lam .. | .forallE .. =>
    mkENodeCore e (ctor := false) (interpreted := false) (generation := generation)
  | .lit .. | .const .. =>
    mkENode e generation
  | .mvar ..
  | .mdata ..
  | .proj .. =>
    trace[grind.issues] "unexpected term during internalization{indentExpr e}"
    mkENodeCore e (ctor := false) (interpreted := false) (generation := generation)
  | .app .. =>
    if (← isLitValue e) then
      -- We do not want to internalize the components of a literal value.
      mkENode e generation
    else e.withApp fun f args => do
      if f.isConstOf ``Lean.Grind.nestedProof && args.size == 2 then
        -- We only internalize the proposition. We can skip the proof because of
        -- proof irrelevance
        let c := args[0]!
        internalize c generation
        registerParent e c
      else
        unless f.isConst do
          internalize f generation
          registerParent e f
        for h : i in [: args.size] do
          let arg := args[i]
          internalize arg generation
          registerParent e arg
      mkENode e generation
      addCongrTable e

/--
The fields `target?` and `proof?` in `e`'s `ENode` are encoding a transitivity proof
from `e` to the root of the equivalence class
This method "inverts" the proof, and makes it to go from the root of the equivalence class to `e`.

We use this method when merging two equivalence classes.
-/
private partial def invertTrans (e : Expr) : GoalM Unit := do
  go e false none none
where
  go (e : Expr) (flippedNew : Bool) (targetNew? : Option Expr) (proofNew? : Option Expr) : GoalM Unit := do
    let node ← getENode e
    if let some target := node.target? then
      go target (!node.flipped) (some e) node.proof?
    setENode e { node with
      target? := targetNew?
      flipped := flippedNew
      proof?  := proofNew?
    }

private def markAsInconsistent : GoalM Unit :=
  modify fun s => { s with inconsistent := true }

def isInconsistent : GoalM Bool :=
  return (← get).inconsistent

/--
Remove `root` parents from the congruence table.
This is an auxiliary function performed while merging equivalence classes.
-/
private def removeParents (root : Expr) : GoalM ParentSet := do
  let parents ← getParentsAndReset root
  for parent in parents do
    modify fun s => { s with congrTable := s.congrTable.erase { e := parent } }
  return parents

/--
Reinsert parents into the congruence table and detect new equalities.
This is an auxiliary function performed while merging equivalence classes.
-/
private def reinsertParents (parents : ParentSet) : GoalM Unit := do
  for parent in parents do
    addCongrTable parent

private partial def addEqStep (lhs rhs proof : Expr) (isHEq : Bool) : GoalM Unit := do
  trace[grind.eq] "{lhs} {if isHEq then "≡" else "="} {rhs}"
  let lhsNode ← getENode lhs
  let rhsNode ← getENode rhs
  if isSameExpr lhsNode.root rhsNode.root then
    -- `lhs` and `rhs` are already in the same equivalence class.
    trace[grind.debug] "{← ppENodeRef lhs} and {← ppENodeRef rhs} are already in the same equivalence class"
    return ()
  let lhsRoot ← getENode lhsNode.root
  let rhsRoot ← getENode rhsNode.root
  let mut valueInconsistency := false
  if lhsRoot.interpreted && rhsRoot.interpreted then
    if lhsNode.root.isTrue || rhsNode.root.isTrue then
      markAsInconsistent
    else
      valueInconsistency := true
  if    (lhsRoot.interpreted && !rhsRoot.interpreted)
     || (lhsRoot.ctor && !rhsRoot.ctor)
     || (lhsRoot.size > rhsRoot.size && !rhsRoot.interpreted && !rhsRoot.ctor) then
    go rhs lhs rhsNode lhsNode rhsRoot lhsRoot true
  else
    go lhs rhs lhsNode rhsNode lhsRoot rhsRoot false
  -- TODO: propagate value inconsistency
  trace[grind.debug] "after addEqStep, {← ppState}"
  checkInvariants
where
  go (lhs rhs : Expr) (lhsNode rhsNode lhsRoot rhsRoot : ENode) (flipped : Bool) : GoalM Unit := do
    trace[grind.debug] "adding {← ppENodeRef lhs} ↦ {← ppENodeRef rhs}"
    /-
    We have the following `target?/proof?`
    `lhs -> ... -> lhsNode.root`
    `rhs -> ... -> rhsNode.root`
    We want to convert it to
    `lhsNode.root -> ... -> lhs -*-> rhs -> ... -> rhsNode.root`
    where step `-*->` is justified by `proof` (or `proof.symm` if `flipped := true`)
    -/
    invertTrans lhs
    setENode lhs { lhsNode with
      target? := rhs
      proof?  := proof
      flipped
    }
    let parents ← removeParents lhsRoot.self
    -- TODO: set propagateBool
    updateRoots lhs rhsNode.root true -- TODO
    trace[grind.debug] "{← ppENodeRef lhs} new root {← ppENodeRef rhsNode.root}, {← ppENodeRef (← getRoot lhs)}"
    reinsertParents parents
    setENode lhsNode.root { (← getENode lhsRoot.self) with -- We must retrieve `lhsRoot` since it was updated.
      next := rhsRoot.next
    }
    setENode rhsNode.root { rhsRoot with
      next := lhsRoot.next
      size := rhsRoot.size + lhsRoot.size
      hasLambdas := rhsRoot.hasLambdas || lhsRoot.hasLambdas
      heqProofs  := isHEq || rhsRoot.heqProofs || lhsRoot.heqProofs
    }
    copyParentsTo parents rhsNode.root

  updateRoots (lhs : Expr) (rootNew : Expr) (_propagateBool : Bool) : GoalM Unit := do
    let rec loop (e : Expr) : GoalM Unit := do
      -- TODO: propagateBool
      let n ← getENode e
      setENode e { n with root := rootNew }
      if isSameExpr lhs n.next then return ()
      loop n.next
    loop lhs

/-- Ensures collection of equations to be processed is empty. -/
private def resetNewEqs : GoalM Unit :=
  modify fun s => { s with newEqs := #[] }

/-- Pops and returns the next equality to be processed. -/
private def popNextEq? : GoalM (Option NewEq) := do
  let r := (← get).newEqs.back?
  if r.isSome then
    modify fun s => { s with newEqs := s.newEqs.pop }
  return r

private partial def addEqCore (lhs rhs proof : Expr) (isHEq : Bool) : GoalM Unit := do
  addEqStep lhs rhs proof isHEq
  processTodo
where
  processTodo : GoalM Unit := do
    if (← isInconsistent) then
      resetNewEqs
      return ()
    let some { lhs, rhs, proof, isHEq } := (← popNextEq?) | return ()
    addEqStep lhs rhs proof isHEq
    processTodo

def addEq (lhs rhs proof : Expr) : GoalM Unit := do
  addEqCore lhs rhs proof false

def addHEq (lhs rhs proof : Expr) : GoalM Unit := do
  addEqCore lhs rhs proof true

/--
Adds a new `fact` justified by the given proof and using the given generation.
-/
def add (fact : Expr) (proof : Expr) (generation := 0) : GoalM Unit := do
  trace[grind.add] "{proof} : {fact}"
  if (← isInconsistent) then return ()
  resetNewEqs
  let_expr Not p := fact
    | go fact false
  go p true
where
  go (p : Expr) (isNeg : Bool) : GoalM Unit := do
    trace[grind.add] "isNeg: {isNeg}, {p}"
    match_expr p with
    | Eq _ lhs rhs => goEq p lhs rhs isNeg false
    | HEq _ lhs _ rhs => goEq p lhs rhs isNeg true
    | _ =>
      internalize p generation
      if isNeg then
        addEq p (← getFalseExpr) (← mkEqFalse proof)
      else
        addEq p (← getTrueExpr) (← mkEqTrue proof)

  goEq (p : Expr) (lhs rhs : Expr) (isNeg : Bool) (isHEq : Bool) : GoalM Unit := do
    if isNeg then
      internalize p generation
      addEq p (← getFalseExpr) (← mkEqFalse proof)
    else
      internalize lhs generation
      internalize rhs generation
      addEqCore lhs rhs proof isHEq

/--
Adds a new hypothesis.
-/
def addHyp (fvarId : FVarId) (generation := 0) : GoalM Unit := do
  add (← fvarId.getType) (mkFVar fvarId) generation

end Lean.Meta.Grind
