reset_grind_attrs%
set_option warn.sorry false

attribute [grind =] Array.size_set

opaque P : Nat → Prop
opaque Q : Nat → Prop
opaque f : Nat → Nat → Nat

@[grind→] theorem pqf : Q x → P (f x x) := sorry

opaque h : Nat → Nat
opaque g : Nat → Nat → Nat

@[grind _=_]
theorem hg : h x = g x (g x x) := sorry

/--
warning: this parameter is redundant, environment already contains `@[grind =] Array.size_set`
-/
#guard_msgs (warning) in
example : True := by grind [= Array.size_set]

/-- warning: this parameter is redundant, environment already contains `@[grind →] pqf` -/
#guard_msgs (warning) in
example : True := by grind [→ pqf]

/--
warning: this parameter is redundant, environment already contains `@[grind →] pqf`
---
warning: this parameter is redundant, environment already contains `@[grind =] Array.size_set`
-/
#guard_msgs (warning) in
example : True := by grind [→ pqf, = Array.size_set]

/-- warning: this parameter is redundant, environment already contains `@[grind _=_] hg` -/
#guard_msgs (warning) in
example : True := by grind [_=_ hg]

/-- warning: this parameter is redundant, environment already contains `@[grind =_] hg` -/
#guard_msgs (warning) in
example : True := by grind [=_ hg]

#guard_msgs (warning) in
example : True := by grind [Array.size_set]

#guard_msgs (warning) in
example : True := by grind [pqf]

#guard_msgs (warning) in
example : True := by grind [hg]
