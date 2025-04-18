import Lean

namespace Structural
def filter (p : α → Bool) (xs : List α) : List α :=
  match xs with
  | [] => []
  | x::xs =>
    if p x then
      x :: filter p xs
    else
      filter p xs

set_option trace.Meta.FunInd true
run_meta
  let ns ← Lean.Tactic.FunInd.getEqnsFor ``filter
  ns.forM fun n => Lean.logInfo m!"{.signature n}"

end Structural

namespace WF
def filter (p : α → Bool) (xs : List α) : List α :=
  match xs with
  | [] => []
  | x::xs =>
    match p x with
    | true => x :: filter p xs
    | false => filter p xs
termination_by xs

run_meta
  let ns ← Lean.Tactic.FunInd.getEqnsFor ``filter
  ns.forM fun n => Lean.logInfo m!"{.signature n}"

/--
info: WF.filter.fun_cases_eq_1.{u_1} {α : Type u_1} (p : α → Bool) : filter p [] = []
---
info: WF.filter.fun_cases_eq_2.{u_1} {α : Type u_1} (p : α → Bool) (x : α) (xs : List α) (h : p x = true) :
  filter p (x :: xs) = x :: filter p xs
---
info: WF.filter.fun_cases_eq_3.{u_1} {α : Type u_1} (p : α → Bool) (x : α) (xs : List α) (h : ¬p x = true) :
  filter p (x :: xs) = filter p xs
-/
#guard_msgs in
run_meta
  let ns ← Lean.Tactic.FunInd.getEqnsFor ``filter
  ns.forM fun n => Lean.logInfo m!"{.signature n}"

end WF


namespace SiftDown

-- The following function has nested ites. But we only want to split to split
-- those in tail position.

abbrev leftChild (i : Nat) := 2*i + 1
abbrev parent (i : Nat) := (i - 1) / 2

def siftDown (a : Array Int) (root : Nat) (e : Nat) (h : e ≤ a.size) : Array Int :=
  if _ : leftChild root < e then
    let child := leftChild root
    let child := if _ : child+1 < e then
      if a[child]! < a[child + 1]! then
        child + 1
      else
        child
    else
      child
    if a[root]! < a[child]! then
      let a := a.swapIfInBounds root child
      siftDown a child e (h := sorry)
    else
      a
  else
    a
termination_by e - root
decreasing_by sorry

/--
info: SiftDown.siftDown.induct (e : Nat) (motive : (a : Array Int) → Nat → e ≤ a.size → Prop)
  (case1 :
    ∀ (a : Array Int) (root : Nat) (h : e ≤ a.size),
      leftChild root < e →
        let child := leftChild root;
        let child := if x : child + 1 < e then if h : a[child]! < a[child + 1]! then child + 1 else child else child;
        a[root]! < a[child]! →
          let a_1 := a.swapIfInBounds root child;
          motive a_1 child ⋯ → motive a root h)
  (case2 :
    ∀ (a : Array Int) (root : Nat) (h : e ≤ a.size),
      leftChild root < e →
        let child := leftChild root;
        let child := if x : child + 1 < e then if h : a[child]! < a[child + 1]! then child + 1 else child else child;
        ¬a[root]! < a[child]! → motive a root h)
  (case3 : ∀ (a : Array Int) (root : Nat) (h : e ≤ a.size), ¬leftChild root < e → motive a root h) (a : Array Int)
  (root : Nat) (h : e ≤ a.size) : motive a root h
-/
#guard_msgs in #check siftDown.induct

/--
info: SiftDown.siftDown.fun_cases_eq_1 (a : Array Int) (root e : Nat) (h : e ≤ a.size) :
  leftChild root < e →
    let child := leftChild root;
    let child := if x : child + 1 < e then if a[child]! < a[child + 1]! then child + 1 else child else child;
    a[root]! < a[child]! →
      siftDown a root e h =
        let child := leftChild root;
        let child := if x : child + 1 < e then if a[child]! < a[child + 1]! then child + 1 else child else child;
        if a[root]! < a[child]! then
          let a_1 := a.swapIfInBounds root child;
          siftDown a_1 child e ⋯
        else a
---
info: SiftDown.siftDown.fun_cases_eq_2 (a : Array Int) (root e : Nat) (h : e ≤ a.size) :
  leftChild root < e →
    let child := leftChild root;
    let child := if x : child + 1 < e then if a[child]! < a[child + 1]! then child + 1 else child else child;
    ¬a[root]! < a[child]! →
      siftDown a root e h =
        let child := leftChild root;
        let child := if x : child + 1 < e then if a[child]! < a[child + 1]! then child + 1 else child else child;
        if a[root]! < a[child]! then
          let a_1 := a.swapIfInBounds root child;
          siftDown a_1 child e ⋯
        else a
---
info: SiftDown.siftDown.fun_cases_eq_3 (a : Array Int) (root e : Nat) (h : e ≤ a.size) :
  ¬leftChild root < e → siftDown a root e h = a
-/
#guard_msgs in
run_meta
  let ns ← Lean.Tactic.FunInd.getEqnsFor ``siftDown
  ns.forM fun n => Lean.logInfo m!"{.signature n}"

end SiftDown
