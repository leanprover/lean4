def replace (f : Nat → Option Nat) (t : Nat) : Nat :=
  match f t with
  | some u => u
  | none =>
    match t with
    | .zero => .zero
    | .succ t' => replace f t'

/--
info: equations:
theorem replace.eq_1 : ∀ (f : Nat → Option Nat),
  replace f Nat.zero =
    match f Nat.zero with
    | some u => u
    | none => Nat.zero
theorem replace.eq_2 : ∀ (f : Nat → Option Nat) (t' : Nat),
  replace f t'.succ =
    match f t'.succ with
    | some u => u
    | none => replace f t'
-/
#guard_msgs in
#print equations replace

/--
error: Failed to realize constant replace.eq_def:
  failed to generate unfold theorem for 'replace'
  case h_1
  f : Nat → Option Nat
  t : Nat
  x : Option Nat
  u : Nat
  heq✝ : f t = some u
  ⊢ replace f t = u
---
error: Failed to realize constant replace.eq_def:
  failed to generate unfold theorem for 'replace'
  case h_1
  f : Nat → Option Nat
  t : Nat
  x : Option Nat
  u : Nat
  heq✝ : f t = some u
  ⊢ replace f t = u
---
error: unknown identifier 'replace.eq_def'
-/
#guard_msgs in
#check replace.eq_def

def replace2 (f : Nat → Option Nat) (t1 t2 : Nat) : Nat :=
  match f t1 with
  | some u => u
  | none =>
    match t2 with
    | .zero => .zero
    | .succ t' => replace2 f t1 t'

/--
info: equations:
theorem replace2.eq_1 : ∀ (f : Nat → Option Nat) (t1 : Nat),
  replace2 f t1 Nat.zero =
    match f t1 with
    | some u => u
    | none => Nat.zero
theorem replace2.eq_2 : ∀ (f : Nat → Option Nat) (t1 t' : Nat),
  replace2 f t1 t'.succ =
    match f t1 with
    | some u => u
    | none => replace2 f t1 t'
-/
#guard_msgs in
#print equations replace2

/--
error: Failed to realize constant replace2.eq_def:
  failed to generate unfold theorem for 'replace2'
  case h_1
  f : Nat → Option Nat
  t1 t2 : Nat
  x : Option Nat
  u : Nat
  heq✝ : f t1 = some u
  ⊢ replace2 f t1 t2 = u
---
error: Failed to realize constant replace2.eq_def:
  failed to generate unfold theorem for 'replace2'
  case h_1
  f : Nat → Option Nat
  t1 t2 : Nat
  x : Option Nat
  u : Nat
  heq✝ : f t1 = some u
  ⊢ replace2 f t1 t2 = u
---
error: unknown identifier 'replace2.eq_def'
-/
#guard_msgs in
#check replace2.eq_def
