/-!
# `congr` conv tactic with "over-applied" functions
-/

/-!
The function `g` is "over-applied". Previously, conv-mode `congr` failed.
-/
/--
info: case a
a b : Nat
g : {α : Type} → α → α
f : Nat → Nat
h : a = b
| f

case a
a b : Nat
g : {α : Type} → α → α
f : Nat → Nat
h : a = b
| a
-/
#guard_msgs in
example (a b : Nat) (g : {α : Type} → α → α) (f : Nat → Nat) (h : a = b) : g f a = g f b := by
  conv =>
    lhs
    congr
    trace_state
    · rfl
    · rw [h]

example (a b : Nat) (g : {α : Type} → α → α) (f : Nat → Nat) (h : a = b) : g f a = g f b := by
  conv =>
    lhs
    arg 2
    rw [h]
