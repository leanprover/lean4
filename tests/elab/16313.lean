/-!
Regression test for #16313: `cbv` was slow on a `match` whose discriminant fails to match a
`String` literal pattern and falls through to a later alternative. `cbv` now discharges the overlap
hypotheses of the match equations instead of reducing the matcher with `whnf`.
-/

def onString : String → Nat
  | "registered_name" => 1
  | _ => 2

def onNat : Nat → Nat
  | 1234567 => 1
  | _ => 2

def onChar : Char → Nat
  | 'r' => 1
  | _ => 2

theorem string_falls : onString "trap_exit" = 2 := by cbv
theorem string_matches : onString "registered_name" = 1 := by cbv
theorem nat_falls : onNat 7654321 = 2 := by cbv
theorem char_falls : onChar 't' = 2 := by cbv
theorem string_ite : (if "trap_exit" = "registered_name" then 1 else 2) = 2 := by cbv

def two : String → String → Nat
  | "a", "b" => 1
  | _, _ => 2

def three : String → Nat
  | "a" => 1
  | "b" => 2
  | "c" => 3
  | _ => 4

inductive Term where
  | atom : String → Term
  | other : Term

def onAtom : Term → Nat
  | .atom "registered_name" => 1
  | _ => 2

def onAtom2 : Term → Nat
  | .atom "registered_name" => 1
  | .atom _ => 3
  | .other => 0

/-! Falling through a literal pattern uses the match equations, not `recMatcher`. -/

set_option trace.Meta.Tactic.cbv.rewrite true

#guard_msgs in
theorem string_falls' : onString "trap_exit" = 2 := by cbv

/-! Overlap hypothesis `x = "a" → x_1 = "b" → False`, refuted by either premise. -/

#guard_msgs in
theorem two_falls_snd : two "a" "c" = 2 := by cbv

#guard_msgs in
theorem two_falls_fst : two "x" "b" = 2 := by cbv

/-! Several earlier alternatives, so several overlap hypotheses. -/

/--
trace: [Meta.Tactic.cbv.rewrite] equation `three`:
      three "c"
    ==>
      3
-/
#guard_msgs in
theorem three_mid : three "c" = 3 := by cbv

#guard_msgs in
theorem three_falls : three "z" = 4 := by cbv

/-! The constructor is already split, so the overlap hypothesis is `s = "registered_name" → False`. -/

#guard_msgs in
theorem atom2_falls : onAtom2 (.atom "trap_exit") = 3 := by cbv

/-!
The overlap hypothesis `x = Term.atom "registered_name" → False` needs constructor injectivity,
which `cbv` does not yet use, so this still falls back to `recMatcher`.
-/

/--
trace: [Meta.Tactic.cbv.rewrite] recMatcher:
      match Term.atom "trap_exit" with
      | Term.atom "registered_name" => 1
      | x => 2
    ==>
      2
-/
#guard_msgs in
theorem atom_falls : onAtom (.atom "trap_exit") = 2 := by cbv

/--
trace: [Meta.Tactic.cbv.rewrite] equation `onAtom`:
      onAtom (Term.atom "registered_name")
    ==>
      1
-/
#guard_msgs in
theorem atom_matches : onAtom (.atom "registered_name") = 1 := by cbv
