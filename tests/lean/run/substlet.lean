/-!
# Tests of the `subst` tactic when `let`s are present.
-/

/-!
Eliminates `a` even though `e : id a = m`.
-/
/--
trace: case intro
n : Nat
m : Nat := n
a : Nat
e : id a = m
⊢ 0 + n = n
---
trace: case intro
a : Nat
m : Nat := id a
⊢ 0 + id a = id a
-/
#guard_msgs in
theorem ex1 (n : Nat) : 0 + n = n := by
  let m := n
  have h : ∃ k, id k = m := ⟨m, rfl⟩
  cases h with
  | intro a e =>
    trace_state
    subst e
    trace_state
    apply Nat.zero_add

/-!
Eliminates `a` even though `e : m = id a`.
-/
/--
trace: case intro
n : Nat
m : Nat := n
a : Nat
e : m = id a
⊢ 0 + n = n
---
trace: case intro
n : Nat
m : Nat := n
⊢ 0 + n = n
-/
#guard_msgs in
theorem ex2 (n : Nat) : 0 + n = n := by
  let m := n
  have h : ∃ k, m = id k := ⟨m, rfl⟩
  cases h with
  | intro a e =>
    trace_state
    subst e
    trace_state
    apply Nat.zero_add

/-!
Since `v` is a let binding, the `subst v` tactic instead
zeta delta reduces it everywhere and then clears it.
-/
/--
trace: n : Nat
h : n = 0
m : Nat := n + 1
v : Nat := m + 1
this : v = n + 2
⊢ 0 + n = 0
---
trace: n : Nat
h : n = 0
m : Nat := n + 1
this : m + 1 = n + 2
⊢ 0 + n = 0
---
trace: m : Nat := 0 + 1
this : m + 1 = 0 + 2
⊢ 0 + 0 = 0
-/
#guard_msgs in
theorem ex3 (n : Nat) (h : n = 0) : 0 + n = 0 := by
  let m := n + 1
  let v := m + 1
  have : v = n + 2 := rfl
  trace_state
  subst v
  trace_state
  subst n
  trace_state
  rfl

/-!
Can't do `subst this` with `this : v = n + 2` since `v` is a let binding.
The tactic sees `m + 1 = n + 2` and fails.
-/
/--
error: Tactic `subst` failed: invalid equality proof, it is not of the form (x = t) or (t = x)
  v = n + 2

n : Nat
h : n = 0
m : Nat := n + 1
v : Nat := m + 1
this : v = n + 2
⊢ 0 + n = 0
-/
#guard_msgs in
theorem ex4 (n : Nat) (h : n = 0) : 0 + n = 0 := by
  let m := n + 1
  let v := m + 1
  have : v = n + 2 := rfl
  subst this
