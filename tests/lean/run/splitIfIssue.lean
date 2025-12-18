import Lean.Elab.Tactic.Location
import Lean.Meta.Tactic.SplitIf
import Lean.Elab.Tactic.Simp

section Mathlib.Tactic.Core

open Lean Elab Tactic

namespace Lean.Elab.Tactic
#check Parser.Tactic.allGoals
def allGoals (tac : TacticM Unit) : TacticM Unit := do
  let mvarIds ← getGoals
  let mut mvarIdsNew := #[]
  for mvarId in mvarIds do
    unless (← mvarId.isAssigned) do
      setGoals [mvarId]
      try
        tac
        mvarIdsNew := mvarIdsNew ++ (← getUnsolvedGoals)
      catch ex =>
        if (← read).recover then
          logException ex
          mvarIdsNew := mvarIdsNew.push mvarId
        else
          throw ex
  setGoals mvarIdsNew.toList

/-- Simulates the `<;>` tactic combinator. First runs `tac1` and then runs
    `tac2` on all newly-generated subgoals.
-/
def andThenOnSubgoals (tac1 : TacticM Unit) (tac2 : TacticM Unit) : TacticM Unit :=
  focus do tac1; allGoals tac2

end Lean.Elab.Tactic

end Mathlib.Tactic.Core

section Mathlib.Tactic.SplitIfs

namespace Mathlib.Tactic

open Lean Elab.Tactic Parser.Tactic Lean.Meta

/-- A position where a split may apply.
-/
private inductive SplitPosition
| target
| hyp (fvarId: FVarId)

/-- Collects a list of positions pointed to by `loc` and their types.
-/
private def getSplitCandidates (loc : Location) : TacticM (List (SplitPosition × Expr)) :=
match loc with
| Location.wildcard => do
   let candidates ← (← getLCtx).getFVarIds.mapM
     (fun fvarId ↦ do
       let typ ← instantiateMVars (← inferType (mkFVar fvarId))
       return (SplitPosition.hyp fvarId, typ))
   pure ((SplitPosition.target, ← getMainTarget) :: candidates.toList)
| Location.targets hyps tgt => do
   let candidates ← (← hyps.mapM getFVarId).mapM
     (fun fvarId ↦ do
       let typ ← instantiateMVars (← inferType (mkFVar fvarId))
       return (SplitPosition.hyp fvarId, typ))
   if tgt
   then return (SplitPosition.target, ← getMainTarget) :: candidates.toList
   else return candidates.toList

/-- Return the condition and decidable instance of an `if` expression to case split. -/
private partial def findIfToSplit? (e : Expr) : Option (Expr × Expr) :=
  match e.find? fun e => (e.isIte || e.isDIte) && !(e.getArg! 1 5).hasLooseBVars with
  | some iteApp =>
    let cond := iteApp.getArg! 1 5
    let dec := iteApp.getArg! 2 5
    -- Try to find a nested `if` in `cond`
    findIfToSplit? cond |>.getD (cond, dec)
  | none => none

/-- Finds an if condition to split. If successful, returns the position and the condition.
-/
private def findIfCondAt (loc : Location) : TacticM (Option (SplitPosition × Expr)) := do
  for (pos, e) in (← getSplitCandidates loc) do
    if let some (cond, _) := findIfToSplit? e
    then return some (pos, cond)
  return none

/-- `Simp.Discharge` strategy to use in `reduceIfsAt`. Delegates to
`SplitIf.discharge?`, and additionally supports discharging `True`, to
better match the behavior of mathlib3's `split_ifs`.
-/
private def discharge? (e : Expr) : SimpM (Option Expr) := do
  let e ← instantiateMVars e
  if let some e1 ← (← SplitIf.mkDischarge? false) e
    then return some e1
  if e.isConstOf `True
    then return some (mkConst `True.intro)
  return none

/-- Simplifies if-then-else expressions after cases have been split out.
-/
private def reduceIfsAt (loc : Location) : TacticM Unit := do
  let ctx ← SplitIf.getSimpContext
  let ctx ← ctx.setConfig { ctx.config with failIfUnchanged := false }
  let _ ← simpLocation ctx (← ({} : Simp.SimprocsArray).add `reduceCtorEq false) discharge? loc
  pure ()

/-- Splits a single if-then-else expression and then reduces the resulting goals.
Has a similar effect as `SplitIf.splitIfTarget?` or `SplitIf.splitIfLocalDecl?` from
core Lean 4. We opt not to use those library functions so that we can better mimic
the behavior of mathlib3's `split_ifs`.
-/
private def splitIf1 (cond : Expr) (hName : Name) (loc : Location) : TacticM Unit := do
  let splitCases :=
    evalTactic (← `(tactic| by_cases $(mkIdent hName) : $(← Elab.Term.exprToSyntax cond)))
  andThenOnSubgoals splitCases (reduceIfsAt loc)

/-- Pops off the front of the list of names, or generates a fresh name if the
list is empty.
-/
private def getNextName (hNames: IO.Ref (List (TSyntax `Lean.binderIdent))) : MetaM Name := do
  match ← hNames.get with
  | [] => mkFreshUserName `h
  | n::ns => do hNames.set ns
                if let `(binderIdent| $x:ident) := n
                then pure x.getId
                else pure `_

/-- Returns `true` if the condition or its negation already appears as a hypothesis.
-/
private def valueKnown (cond : Expr) : TacticM Bool := do
  let not_cond := mkApp (mkConst `Not) cond
  for h in ← getLocalHyps do
    let ty ← instantiateMVars (← inferType h)
    if cond == ty then return true
    if not_cond == ty then return true
  return false

/-- Main loop of split_ifs. Pulls names for new hypotheses from `hNames`.
Stops if it encounters a condition in the passed-in `List Expr`.
-/
private partial def splitIfsCore
    (loc : Location)
    (hNames : IO.Ref (List (TSyntax `Lean.binderIdent))) :
    List Expr → TacticM Unit := fun done ↦ withMainContext do
  let some (_,cond) ← findIfCondAt loc
      | Meta.throwTacticEx `split_ifs (← getMainGoal) "no if-then-else conditions to split"

  -- If `cond` is `¬p` then use `p` instead.
  let cond := if cond.isAppOf `Not then cond.getAppArgs[0]! else cond

  if done.contains cond then return ()
  let no_split ← valueKnown cond
  if no_split then
    andThenOnSubgoals (reduceIfsAt loc) (splitIfsCore loc hNames (cond::done) <|> pure ())
  else do
    let hName ← getNextName hNames
    andThenOnSubgoals (splitIf1 cond hName loc) ((splitIfsCore loc hNames (cond::done)) <|>
      pure ())

/-- Splits all if-then-else-expressions into multiple goals.
Given a goal of the form `g (if p then x else y)`, `split_ifs` will produce
two goals: `p ⊢ g x` and `¬p ⊢ g y`.
If there are multiple ite-expressions, then `split_ifs` will split them all,
starting with a top-most one whose condition does not contain another
ite-expression.
`split_ifs at *` splits all ite-expressions in all hypotheses as well as the goal.
`split_ifs with h₁ h₂ h₃` overrides the default names for the hypotheses.
-/
syntax (name := splitIfs) "split_ifs" (location)? (" with" (ppSpace colGt binderIdent)+)? : tactic

elab_rules : tactic
| `(tactic| split_ifs $[$loc:location]? $[with $withArg*]?) =>
  let loc := match loc with
  | none => Location.targets #[] true
  | some loc => expandLocation loc
  let names := match withArg with
  | none => []
  | some args => args.toList
  withMainContext do
    let names ← IO.mkRef names
    splitIfsCore loc names []
    for name in ← names.get do
      logWarningAt name m!"unused name: {name}"

end Mathlib.Tactic

end Mathlib.Tactic.SplitIfs

section Mathlib.Order.Defs

class Preorder (α : Type _) extends LE α, LT α where

class PartialOrder (α : Type _) extends Preorder α where

class LinearOrder (α : Type _) extends PartialOrder α, Min α, Max α, Ord α where
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  decidableLE : DecidableRel (· ≤ · : α → α → Prop)
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  decidableEq : DecidableEq α
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  decidableLT : DecidableRel (· < · : α → α → Prop)
  min := fun a b => if a ≤ b then a else b
  max := fun a b => if a ≤ b then b else a

variable [LinearOrder α] {a b c : α}

instance (priority := 900) (a b : α) : Decidable (a < b) := LinearOrder.decidableLT a b
instance (priority := 900) (a b : α) : Decidable (a ≤ b) := LinearOrder.decidableLE a b
instance (priority := 900) (a b : α) : Decidable (a = b) := LinearOrder.decidableEq a b

end Mathlib.Order.Defs

section Mathlib.Order.Lattice

universe u v w

variable {α : Type u}

class SemilatticeSup (α : Type u) extends PartialOrder α where
  sup : α → α → α

class Lattice (α : Type u) extends SemilatticeSup α

end Mathlib.Order.Lattice

open Lean Meta Elab Tactic in
/-- `guard_goal_nums n` succeeds if there are exactly `n` goals and fails otherwise. -/
elab (name := guardGoalNums) "guard_goal_nums " n:num : tactic => do
  let numGoals := (← getGoals).length
  guard (numGoals = n.getNat) <|>
    throwError "expected {n.getNat} goals but found {numGoals}"

example (a m tl : α) (f : α → β) [LinearOrder β] :
    (if f (if f a < f m then m else a) < f tl then some tl else some (if f a < f m then m else a)) =
      if f a < f (if f m < f tl then tl else m) then some (if f m < f tl then tl else m) else some a := by
  split_ifs
  guard_goal_nums 7
  all_goals sorry

instance LinearOrder.toLattice {α : Type u} [o : LinearOrder α] : Lattice α :=
  let __spread := o
  { __spread with sup := max }

example (a m tl : α) (f : α → β) [LinearOrder β] :
    (if f (if f a < f m then m else a) < f tl then some tl else some (if f a < f m then m else a)) =
      if f a < f (if f m < f tl then tl else m) then some (if f m < f tl then tl else m) else some a := by
  split_ifs
  guard_goal_nums 7
  all_goals sorry
