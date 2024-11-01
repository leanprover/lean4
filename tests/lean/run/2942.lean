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

/-!
While we are here, test `arg` too via `enter`.
-/

/--
info: a b : Nat
g : {α : Type} → α → α
f : Nat → Nat
h : a = b
| a
---
info: a b : Nat
g : {α : Type} → α → α
f : Nat → Nat
h : a = b
| f
---
info: a b : Nat
g : {α : Type} → α → α
f : Nat → Nat
h : a = b
| a
-/
#guard_msgs in
example (a b : Nat) (g : {α : Type} → α → α) (f : Nat → Nat) (h : a = b) : g f a = g f b := by
  conv =>
    conv => enter [1,2]; trace_state
    conv => enter [1,1]; trace_state
    conv => enter [1,@3]; trace_state
    conv => fail_if_success enter [1,@1] -- cannot select the `Type` argument due to dependence.
    rw [h]
