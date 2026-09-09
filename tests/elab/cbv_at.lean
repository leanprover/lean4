/-!
Tests for the `cbv at` location syntax: reducing hypotheses (`at h`), hypotheses
plus target (`at h |-`), and the wildcard (`at *`), which visits the target and
all non-dependent propositional hypotheses. Each location is reduced in its own
`SymM` session, and hypotheses keep their position in the local context.
-/

set_option linter.unusedVariables false

/--
trace: h : True
⊢ True
-/
#guard_msgs in
example (h : 2 + 3 = 5) : True := by
  cbv at h
  trace_state
  trivial

-- False equation in hypothesis: goal is closed automatically
example (h : 2 + 3 = 6) : 42 = 0 := by
  cbv at h

-- `cbv at h |-` — reduces both hypothesis and target
example (h : 2 + 3 = 5) : 1 + 1 = 2 := by
  cbv at h |-

-- Multiple explicit hypotheses
/--
trace: h₁ h₂ : True
⊢ True
-/
#guard_msgs in
example (h₁ : 2 + 3 = 5) (h₂ : 1 + 1 = 2) : True := by
  cbv at h₁ h₂
  trace_state
  trivial

/--
trace: h₁ h₂ : True
⊢ False
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (h₁ : 2 + 3 = 5) (h₂ : 1 + 1 = 2) : False := by
  cbv at *
  trace_state
  sorry

-- Reduces hypothesis but not target when only hypothesis is specified
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (h : (fun x => x + 1) 0 = 1) : 2 + 2 = 5 := by
  cbv at h
  sorry

-- Hypotheses keep their position in the local context
/--
trace: n : Nat
h₁ : True
h₂ : n = 0
⊢ n = 0
-/
#guard_msgs in
example (n : Nat) (h₁ : 2 + 3 = 5) (h₂ : n = 0) : n = 0 := by
  cbv at h₁
  trace_state
  exact h₂

-- `at *` skips hypotheses that other hypotheses depend on: `p` stays unreduced
-- (it would become `True` if visited) because `h` mentions it. `h` itself is a
-- non-dependent proposition, so it is reduced, as is `h'`.
/--
trace: p : 2 + 3 = 5
h h' : True
⊢ True
-/
#guard_msgs in
example (p : 2 + 3 = 5) (h : p = p) (h' : 1 + 1 = 2) : True := by
  cbv at *
  trace_state
  trivial

-- `at *` skips non-propositional hypotheses: `x` would become `Fin 5` if visited
/--
trace: x : Fin (2 + 3)
h : True
⊢ True
-/
#guard_msgs in
example (x : Fin (2 + 3)) (h : 1 + 1 = 2) : True := by
  cbv at *
  trace_state
  trivial

-- `at *` skips hypotheses occurring in the target: `q` stays unreduced. The
-- target `P q` is still visited but has no reduction.
/--
trace: P : 2 + 3 = 5 → Prop
q : 2 + 3 = 5
hp : P q
h : True
⊢ P q
-/
#guard_msgs in
example (P : (2 + 3 = 5) → Prop) (q : 2 + 3 = 5) (hp : P q) (h : 1 + 1 = 2) : P q := by
  cbv at *
  trace_state
  exact hp
