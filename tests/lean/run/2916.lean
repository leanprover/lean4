set_option pp.coercions false -- Show `OfNat.ofNat` when present for clarity

/--
info: x : Nat
⊢ OfNat.ofNat 2 = x
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : nat_lit 2 = x := by
  simp only
  trace_state
  sorry

/--
info: x : Nat
⊢ OfNat.ofNat 2 = x
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : nat_lit 2 = x := by
  dsimp only -- dsimp made no progress
  trace_state
  sorry

/--
info: α : Nat → Type
f : (n : Nat) → α n
x : α (OfNat.ofNat 2)
⊢ f (OfNat.ofNat 2) = x
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (α : Nat → Type) (f : (n : Nat) → α n) (x : α 2) : f (nat_lit 2) = x := by
  simp only
  trace_state
  sorry

/--
info: x : Nat
f : Nat → Nat
h : f (OfNat.ofNat 2) = x
⊢ f (OfNat.ofNat 2) = x
---
info: x : Nat
f : Nat → Nat
h : f (OfNat.ofNat 2) = x
⊢ f 2 = x
-/
#guard_msgs in
example (f : Nat → Nat) (h : f 2 = x) : f 2 = x := by
  trace_state
  simp [OfNat.ofNat]
  trace_state
  assumption

/--
info: α : Nat → Type
f : (n : Nat) → α n
x : α (OfNat.ofNat 2)
⊢ f (OfNat.ofNat 2) = x
---
info: α : Nat → Type
f : (n : Nat) → α n
x : α (OfNat.ofNat 2)
⊢ f 2 = x
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (α : Nat → Type) (f : (n : Nat) → α n) (x : α 2) : f 2 = x := by
  trace_state
  simp [OfNat.ofNat]
  trace_state
  sorry
