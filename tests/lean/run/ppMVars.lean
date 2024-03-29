/-!
# Testing `pp.mvars`
-/

/-!
Default values
-/

/-- info: ?a : Nat -/
#guard_msgs in #check (?a : Nat)

/-!
Turning off `pp.mvars`
-/
section
set_option pp.mvars false

/-- info: ?_ : Nat -/
#guard_msgs in #check (?a : Nat)

/-- info: ?_ : Nat -/
#guard_msgs in #check (_ : Nat)

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
