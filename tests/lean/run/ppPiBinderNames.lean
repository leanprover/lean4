/-!
# Testing pretty printing option `pp.piBinderNames`
-/

/-!
Tests of default options.
-/
section

/-!
Unused name, doesn't print.
-/
/-- info: Nat → Type : Type 1 -/
#guard_msgs in #check (x : Nat) → Type

/-!
Unused hygienic name, doesn't print.
-/
/-- info: Nat → Type : Type 1 -/
#guard_msgs in #check Nat → Type

end

/-!
Tests with `pp.piBinderNames` enabled.
-/
section
set_option pp.piBinderNames true

/-!
Unused name, prints since not hygienic.
-/
/-- info: (x : Nat) → Type : Type 1 -/
#guard_msgs in #check (x : Nat) → Type

/-!
Unused hygienic name, doesn't print.
-/
/-- info: Nat → Type : Type 1 -/
#guard_msgs in #check Nat → Type

end

/-!
Tests with `pp.piBinderNames` and `pp.piBinderNames.hygienic` enabled.
-/
section
set_option pp.piBinderNames true
set_option pp.piBinderNames.hygienic true

/-!
Prints unused name.
-/
/-- info: (x : Nat) → Type : Type 1 -/
#guard_msgs in #check (x : Nat) → Type

/-!
Prints unused hygienic name.
-/
/-- info: (a : Nat) → Type : Type 1 -/
#guard_msgs in #check Nat → Type

end

/-!
Tests with `pp.all`. Enables `pp.piBinderNames`.
-/
section
set_option pp.all true

/-!
Unused name, prints since not hygienic.
-/
/-- info: (x : Nat) → Type : Type 1 -/
#guard_msgs in #check (x : Nat) → Type

/-!
Unused hygienic name, doesn't print.
-/
/-- info: Nat → Type : Type 1 -/
#guard_msgs in #check Nat → Type

set_option pp.piBinderNames.hygienic true

/-!
Prints unused name.
-/
/-- info: (x : Nat) → Type : Type 1 -/
#guard_msgs in #check (x : Nat) → Type

/-!
Prints unused hygienic name.
-/
/-- info: (a : Nat) → Type : Type 1 -/
#guard_msgs in #check Nat → Type

end
