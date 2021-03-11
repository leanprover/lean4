import Lean

universe u

inductive Pred : ∀ (α : Type u), List α → Type (u+1)
| foo {α : Type u} (l1 : List α) (l2 : List (Option α)) : Pred (Option α) l2 → Pred α l1

axiom goal : forall (α : Type u) (xs : List (List α)) (h : Pred (List α) xs), xs ≠ [] → xs = xs

open Lean
open Lean.Meta

def tst1 : MetaM Unit := do
let cinfo ← getConstInfo `goal;
let type := cinfo.type;
let mvar   ← mkFreshExprMVar type;
trace[Elab] (MessageData.ofGoal mvar.mvarId!);
let (_, mvarId) ← introN mvar.mvarId! 2;
let (fvarId, mvarId) ← intro1 mvarId;
trace[Elab] (MessageData.ofGoal mvarId);
let s ← generalizeIndices mvarId fvarId;
trace[Elab] (MessageData.ofGoal s.mvarId);
pure ()

set_option trace.Elab true

#eval tst1
