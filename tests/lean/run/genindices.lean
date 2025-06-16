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
let (_, mvarId) ← mvar.mvarId!.introN 2;
let (fvarId, mvarId) ← mvarId.intro1;
trace[Elab] (MessageData.ofGoal mvarId);
let s ← generalizeIndices mvarId fvarId;
trace[Elab] (MessageData.ofGoal s.mvarId);
pure ()

set_option trace.Elab true

/--
info: [Elab] ⊢ ∀ (α : Type u) (xs : List (List α)) (h : Pred (List α) xs), xs ≠ [] → xs = xs
[Elab] α✝ : Type u
    xs✝ : List (List α✝)
    h✝ : Pred (List α✝) xs✝
    ⊢ xs✝ ≠ [] → xs✝ = xs✝
[Elab] α✝ : Type u
    xs✝ : List (List α✝)
    h✝¹ : Pred (List α✝) xs✝
    α : Type u
    a✝ : List α
    h✝ : Pred α a✝
    ⊢ List α✝ = α → HEq xs✝ a✝ → HEq h✝¹ h✝ → xs✝ ≠ [] → xs✝ = xs✝
-/
#guard_msgs in
#eval tst1
