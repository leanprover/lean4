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
info: equations:
theorem Structural.filter.eq_1.{u_1} : ∀ {α : Type u_1} (p : α → Bool), filter p [] = []
theorem Structural.filter.eq_2.{u_1} : ∀ {α : Type u_1} (p : α → Bool) (x : α) (xs_2 : List α),
  filter p (x :: xs_2) = if p x = true then x :: filter p xs_2 else filter p xs_2
-/
#guard_msgs in
#print equations filter

/--
info: equations:
theorem Structural.filter.feq_1.{u_1} : ∀ {α : Type u_1} (p : α → Bool), filter p [] = []
theorem Structural.filter.feq_2.{u_1} : ∀ {α : Type u_1} (p : α → Bool) (x : α) (xs_2 : List α),
  p x = true → filter p (x :: xs_2) = x :: filter p xs_2
theorem Structural.filter.feq_3.{u_1} : ∀ {α : Type u_1} (p : α → Bool) (x : α) (xs_2 : List α),
  ¬p x = true → filter p (x :: xs_2) = filter p xs_2
-/
#guard_msgs in
#print fine equations filter

end Structural

namespace WF
def filter (p : α → Bool) (xs : List α) : List α :=
  match xs with
  | [] => []
  | x::xs =>
    if p x then
      x :: filter p xs
    else
      filter p xs
termination_by xs

/--
info: equations:
theorem WF.filter.eq_1.{u_1} : ∀ {α : Type u_1} (p : α → Bool), filter p [] = []
theorem WF.filter.eq_2.{u_1} : ∀ {α : Type u_1} (p : α → Bool) (x : α) (xs_2 : List α),
  filter p (x :: xs_2) = if p x = true then x :: filter p xs_2 else filter p xs_2
-/
#guard_msgs in
#print equations filter

/--
info: equations:
theorem WF.filter.feq_1.{u_1} : ∀ {α : Type u_1} (p : α → Bool), filter p [] = []
theorem WF.filter.feq_2.{u_1} : ∀ {α : Type u_1} (p : α → Bool) (x : α) (xs_2 : List α),
  p x = true → filter p (x :: xs_2) = x :: filter p xs_2
theorem WF.filter.feq_3.{u_1} : ∀ {α : Type u_1} (p : α → Bool) (x : α) (xs_2 : List α),
  ¬p x = true → filter p (x :: xs_2) = filter p xs_2
-/
#guard_msgs in
#print fine equations filter

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
info: equations:
theorem SiftDown.siftDown.feq_1 : ∀ (a : Array Int) (root e : Nat) (h : e ≤ a.size)
  (h_1 : a[leftChild root]! < a[leftChild root + 1]!) (h_2 : leftChild root + 1 < e),
  leftChild root < e →
    leftChild root + 1 < e →
      a[root]! < a[leftChild root + 1]! →
        siftDown a root e h = siftDown (a.swapIfInBounds root (leftChild root + 1)) (leftChild root + 1) e ⋯
theorem SiftDown.siftDown.feq_2 : ∀ (a : Array Int) (root e : Nat) (h : e ≤ a.size) (h_1 : leftChild root + 1 < e)
  (h_2 : a[leftChild root]! < a[leftChild root + 1]!),
  ¬leftChild root + 1 < e →
    siftDown a root e h = siftDown (a.swapIfInBounds root (leftChild root + 1)) (leftChild root + 1) e ⋯
theorem SiftDown.siftDown.feq_3 : ∀ (a : Array Int) (root e : Nat) (h : e ≤ a.size),
  leftChild root < e →
    leftChild root + 1 < e →
      a[leftChild root]! < a[leftChild root + 1]! → ¬a[root]! < a[leftChild root + 1]! → siftDown a root e h = a
theorem SiftDown.siftDown.feq_4 : ∀ (a : Array Int) (root e : Nat) (h : e ≤ a.size)
  (h_1 : ¬a[leftChild root]! < a[leftChild root + 1]!) (h_2 : leftChild root + 1 < e),
  leftChild root < e →
    leftChild root + 1 < e →
      a[root]! < a[leftChild root]! →
        siftDown a root e h = siftDown (a.swapIfInBounds root (leftChild root)) (leftChild root) e ⋯
theorem SiftDown.siftDown.feq_5 : ∀ (a : Array Int) (root e : Nat) (h : e ≤ a.size) (h_1 : leftChild root + 1 < e)
  (h_2 : ¬a[leftChild root]! < a[leftChild root + 1]!),
  ¬leftChild root + 1 < e → siftDown a root e h = siftDown (a.swapIfInBounds root (leftChild root)) (leftChild root) e ⋯
theorem SiftDown.siftDown.feq_6 : ∀ (a : Array Int) (root e : Nat) (h : e ≤ a.size),
  leftChild root < e →
    leftChild root + 1 < e →
      ¬a[leftChild root]! < a[leftChild root + 1]! → ¬a[root]! < a[leftChild root]! → siftDown a root e h = a
theorem SiftDown.siftDown.feq_7 : ∀ (a : Array Int) (root e : Nat) (h : e ≤ a.size) (h_1 : leftChild root + 1 < e)
  (h_2 : a[leftChild root]! < a[leftChild root + 1]!),
  ¬leftChild root + 1 < e →
    siftDown a root e h = siftDown (a.swapIfInBounds root (leftChild root + 1)) (leftChild root + 1) e ⋯
theorem SiftDown.siftDown.feq_8 : ∀ (a : Array Int) (root e : Nat) (h : e ≤ a.size) (h_1 : leftChild root + 1 < e)
  (h_2 : ¬a[leftChild root]! < a[leftChild root + 1]!),
  ¬leftChild root + 1 < e → siftDown a root e h = siftDown (a.swapIfInBounds root (leftChild root)) (leftChild root) e ⋯
theorem SiftDown.siftDown.feq_9 : ∀ (a : Array Int) (root e : Nat) (h : e ≤ a.size) (h_1 : ¬leftChild root + 1 < e),
  leftChild root < e →
    ¬leftChild root + 1 < e →
      a[root]! < a[leftChild root]! →
        siftDown a root e h = siftDown (a.swapIfInBounds root (leftChild root)) (leftChild root) e ⋯
theorem SiftDown.siftDown.feq_10 : ∀ (a : Array Int) (root e : Nat) (h : e ≤ a.size),
  leftChild root < e → ¬leftChild root + 1 < e → ¬a[root]! < a[leftChild root]! → siftDown a root e h = a
theorem SiftDown.siftDown.feq_11 : ∀ (a : Array Int) (root e : Nat) (h : e ≤ a.size),
  ¬leftChild root < e → siftDown a root e h = a
-/
#guard_msgs in
#print fine equations siftDown

end SiftDown
