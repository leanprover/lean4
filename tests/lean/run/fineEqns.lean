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

/--
info: Structural.filter.fun_cases_eq_1.{u_1} {α : Type u_1} (p : α → Bool) : filter p [] = []
---
info: Structural.filter.fun_cases_eq_2.{u_1} {α : Type u_1} (p : α → Bool) (x : α) (xs : List α) (h : p x = true) :
  filter p (x :: xs) = x :: filter p xs
---
info: Structural.filter.fun_cases_eq_3.{u_1} {α : Type u_1} (p : α → Bool) (x : α) (xs : List α) (h : ¬p x = true) :
  filter p (x :: xs) = filter p xs
-/
#guard_msgs in
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

/--
info: WF.filter.fun_cases_eq_1.{u_1} {α : Type u_1} (p : α → Bool) : filter p [] = []
---
info: WF.filter.fun_cases_eq_2.{u_1} {α : Type u_1} (p : α → Bool) (x : α) (xs : List α) :
  p x = true →
    filter p (x :: xs) =
      match p x with
      | true => x :: filter p xs
      | false => filter p xs
---
info: WF.filter.fun_cases_eq_3.{u_1} {α : Type u_1} (p : α → Bool) (x : α) (xs : List α) :
  p x = false →
    filter p (x :: xs) =
      match p x with
      | true => x :: filter p xs
      | false => filter p xs
-/
#guard_msgs in
run_meta
  let ns ← Lean.Tactic.FunInd.getEqnsFor ``filter
  ns.forM fun n => Lean.logInfo m!"{.signature n}"

/--
info: WF.filter.fun_cases_eq_1.{u_1} {α : Type u_1} (p : α → Bool) : filter p [] = []
---
info: WF.filter.fun_cases_eq_2.{u_1} {α : Type u_1} (p : α → Bool) (x : α) (xs : List α) :
  p x = true → filter p (x :: xs) = x :: filter p xs
---
info: WF.filter.fun_cases_eq_3.{u_1} {α : Type u_1} (p : α → Bool) (x : α) (xs : List α) :
  p x = false → filter p (x :: xs) = filter p xs
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

set_option trace.Meta.FunInd true
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
info: SiftDown.siftDown.fun_cases (motive : (a : Array Int) → Nat → (e : Nat) → e ≤ a.size → Prop)
  (case1 :
    ∀ (a : Array Int) (root e : Nat) (h : e ≤ a.size),
      leftChild root < e →
        let child := leftChild root;
        let child := if x : child + 1 < e then if a[child]! < a[child + 1]! then child + 1 else child else child;
        a[root]! < a[child]! → motive a root e h)
  (case2 :
    ∀ (a : Array Int) (root e : Nat) (h : e ≤ a.size),
      leftChild root < e →
        let child := leftChild root;
        let child := if x : child + 1 < e then if a[child]! < a[child + 1]! then child + 1 else child else child;
        ¬a[root]! < a[child]! → motive a root e h)
  (case3 : ∀ (a : Array Int) (root e : Nat) (h : e ≤ a.size), ¬leftChild root < e → motive a root e h) (a : Array Int)
  (root e : Nat) (h : e ≤ a.size) : motive a root e h
-/
#guard_msgs in #check siftDown.fun_cases

/--
info: SiftDown.siftDown.fun_cases_eq_1 (a : Array Int) (root e : Nat) (h : e ≤ a.size) :
  leftChild root < e →
    let child := leftChild root;
    let child := if x : child + 1 < e then if a[child]! < a[child + 1]! then child + 1 else child else child;
    a[root]! < a[child]! →
      siftDown a root e h =
        let a_1 := a.swapIfInBounds root child;
        siftDown a_1 child e ⋯
---
info: SiftDown.siftDown.fun_cases_eq_2 (a : Array Int) (root e : Nat) (h : e ≤ a.size) :
  leftChild root < e →
    let child := leftChild root;
    let child := if x : child + 1 < e then if a[child]! < a[child + 1]! then child + 1 else child else child;
    ¬a[root]! < a[child]! → siftDown a root e h = a
---
info: SiftDown.siftDown.fun_cases_eq_3 (a : Array Int) (root e : Nat) (h : e ≤ a.size) :
  ¬leftChild root < e → siftDown a root e h = a
-/
#guard_msgs in
run_meta
  let ns ← Lean.Tactic.FunInd.getEqnsFor ``siftDown
  ns.forM fun n => Lean.logInfo m!"{.signature n}"

end SiftDown



namespace NestedIf

-- This function has nested `if` where we want to check that the condidion from the inner one
-- does not interfere with the outer one

def foo (xs : List Nat) : Nat :=
  match id xs with
  | [] => 0
  | y::ys =>
    if ys.isEmpty then
      1
    else
      if ys = [y] then
        3
      else
        3

/--
info: NestedIf.foo.fun_cases_eq_1 (xs : List Nat) : id xs = [] → foo xs = 0
---
info: NestedIf.foo.fun_cases_eq_2 (xs : List Nat) (y : Nat) (ys : List Nat) :
  id xs = y :: ys → ∀ (h : ys.isEmpty = true), foo xs = 1
---
info: NestedIf.foo.fun_cases_eq_3 (xs : List Nat) (y : Nat) :
  id xs = [y, y] → ∀ (h : ¬[y].isEmpty = true), foo xs = if [y] = [y] then 3 else 3
-/
#guard_msgs in
run_meta
  let ns ← Lean.Tactic.FunInd.getEqnsFor ``foo
  ns.forM fun n => Lean.logInfo m!"{.signature n}"


end NestedIf

namespace Fib

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fib n + fib (n+1)
termination_by structural x => x


/--
info: Fib.fib.fun_cases_eq_1 : fib 0 = 0
---
info: Fib.fib.fun_cases_eq_2 : fib 1 = 1
---
info: Fib.fib.fun_cases_eq_3 (n : Nat) : fib n.succ.succ = fib n + fib (n + 1)
-/
#guard_msgs in
run_meta
  let ns ← Lean.Tactic.FunInd.getEqnsFor ``fib
  ns.forM fun n => Lean.logInfo m!"{.signature n}"

end Fib
