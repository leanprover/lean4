import Lean

opaque a : Nat
opaque b : Nat

-- Prints the equivalence class containing a `f` application
open Lean Meta Grind in
def fallback : Fallback := do
  let a ← shareCommon <| mkConst ``a
  let b ← shareCommon <| mkConst ``b
  let some h ← mkDiseqProof? a b |
    throwError "terms are not diseq"
  check h
  trace[Meta.debug] "{h} : {← inferType h}"
  assert! (← isDiseq a b)
  assert! (← isDiseq b a)
  let some h' ← mkDiseqProof? b a |
    throwError "terms are not diseq"
  let h' ← mkAppM ``Ne.symm #[h']
  assert! (← isDefEq h h')
  (← get).mvarId.admit

set_option trace.Meta.debug true

/--
trace: [Meta.debug] Lean.Grind.ne_of_ne_of_eq_right h_2 (Lean.Grind.ne_of_ne_of_eq_left h (Ne.symm h_1)) : a ≠ b
-/
#guard_msgs (trace) in
example (x y : Nat) : a = x → y ≠ x → b = y → False := by
  grind on_failure fallback

/--
trace: [Meta.debug] Lean.Grind.ne_of_ne_of_eq_right h_2 (Lean.Grind.ne_of_ne_of_eq_left h h_1) : a ≠ b
-/
#guard_msgs (trace) in
example (x y : Nat) : a = x → x ≠ y → b = y → False := by
  grind on_failure fallback

/--
trace: [Meta.debug] Lean.Grind.ne_of_ne_of_eq_right h_3 (Lean.Grind.ne_of_ne_of_eq_left (Eq.trans h (Eq.symm h_1)) h_2) : a ≠ b
-/
#guard_msgs (trace) in
example (x y z : Nat) : a = x → z = x → z ≠ y → b = y → False := by
  grind on_failure fallback

/-- trace: [Meta.debug] Lean.Grind.ne_of_ne_of_eq_left h (Ne.symm h_1) : a ≠ b -/
#guard_msgs (trace) in
example (x : Nat) : a = x → b ≠ x → False := by
  grind on_failure fallback

/-- trace: [Meta.debug] Lean.Grind.ne_of_ne_of_eq_left h h_1 : a ≠ b -/
#guard_msgs (trace) in
example (x : Nat) : a = x → x ≠ b → False := by
  grind on_failure fallback


/-- trace: [Meta.debug] Lean.Grind.ne_of_ne_of_eq_right h h_1 : a ≠ b -/
#guard_msgs (trace) in
example (x : Nat) : b = x → a ≠ x → False := by
  grind on_failure fallback

/-- trace: [Meta.debug] Lean.Grind.ne_of_ne_of_eq_right h (Ne.symm h_1) : a ≠ b -/
#guard_msgs (trace) in
example (x : Nat) : b = x → x ≠ a → False := by
  grind on_failure fallback

/-- trace: [Meta.debug] Lean.Grind.ne_of_ne_of_eq_left h (Ne.symm h_1) : a ≠ b -/
#guard_msgs (trace) in
example (x : Nat) : a = x → b ≠ x → False := by
  grind on_failure fallback

/-- trace: [Meta.debug] h : ¬a = b -/
#guard_msgs (trace) in
example : a ≠ b → False := by
  grind on_failure fallback

/-- trace: [Meta.debug] Ne.symm h : a ≠ b -/
#guard_msgs (trace) in
example : b ≠ a → False := by
  grind on_failure fallback
