/-- error: Unknown constant `foo` -/
#guard_msgs in
example : False := by
  grind [foo]

/--
error: `grind` failed
case grind
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
-/
#guard_msgs in
example : False := by
  grind +lax [foo]

/-- error: Unknown constant `foo` -/
#guard_msgs in
example : False := by
  grind [-foo]

/--
error: `grind` failed
case grind
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
-/
#guard_msgs in
example : False := by
  grind +lax [-foo]

theorem foo : True := .intro

/--
error: invalid E-matching equality theorem, conclusion must be an equality
  True
-/
#guard_msgs in
example : False := by
  grind [= foo]

/--
error: `grind` failed
case grind
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
-/
#guard_msgs in
example : False := by
  grind +lax [= foo]

theorem bar : Nat = Int := sorry

/--
error: invalid E-matching equality theorem, conclusion must be an equality
  True
-/
#guard_msgs in
example : Int = Nat := by
  grind [= foo, = bar]

#guard_msgs in
example : Int = Nat := by
  grind +lax [= foo, = bar]
