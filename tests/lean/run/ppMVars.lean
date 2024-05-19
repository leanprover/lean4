import Lean.Elab.BuiltinNotation
/-!
# Testing `pp.mvars`
-/

/-!
Default values
-/

/-- info: ?a : Nat -/
#guard_msgs in #check (?a : Nat)

/-- info: ⊢ Sort ?u.1 -/
#guard_msgs (info, drop all) in
example : (by_elab do return .sort (.mvar (.mk (.num `_uniq 1)))) := by
  trace_state
  sorry

/-!
Turning off `pp.mvars`
-/
section
set_option pp.mvars false

/-- info: ?_ : Nat -/
#guard_msgs in #check (?a : Nat)

/-- info: ?_ : Nat -/
#guard_msgs in #check (_ : Nat)

/-- info: ⊢ Sort _ -/
#guard_msgs (info, drop all) in
example : (by_elab do return .sort (.mvar (.mk (.num `_uniq 1)))) := by
  trace_state
  sorry

/-- info: ⊢ Type _ -/
#guard_msgs (info, drop all) in
example : Type _ := by
  trace_state
  sorry

end

/-!
Turning off `pp.mvars` and turning on `pp.mvars.withType`.
-/
section
set_option pp.mvars false
set_option pp.mvars.withType true

/-- info: (?_ : Nat) : Nat -/
#guard_msgs in #check (?a : Nat)

/-- info: (?_ : Nat) : Nat -/
#guard_msgs in #check (_ : Nat)

end

/-!
Turning on `pp.mvars.withType`.
-/
section
set_option pp.mvars.withType true

/-- info: (?a : Nat) : Nat -/
#guard_msgs in #check (?a : Nat)

end
