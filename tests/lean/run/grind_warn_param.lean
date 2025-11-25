module
reset_grind_attrs%
public section
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
warning: this parameter is redundant, environment already contains `Array.size_set` annotated with `@[grind =]`
-/
#guard_msgs (warning) in
example : True := by grind [= Array.size_set]

/--
warning: this parameter is redundant, environment already contains `pqf` annotated with `@[grind →]`
-/
#guard_msgs (warning) in
example : True := by grind [→ pqf]

/--
warning: this parameter is redundant, environment already contains `pqf` annotated with `@[grind →]`
---
warning: this parameter is redundant, environment already contains `Array.size_set` annotated with `@[grind =]`
-/
#guard_msgs (warning) in
example : True := by grind [→ pqf, = Array.size_set]

/--
warning: this parameter is redundant, environment already contains `Array.size_set` annotated with `@[grind =]`
-/
#guard_msgs (warning) in
example : True := by grind [= Array.size_set]

/--
warning: this parameter is redundant, environment already contains `hg` annotated with `@[grind _=_]`
-/
#guard_msgs (warning) in
example : True := by grind [_=_ hg]

/--
warning: this parameter is redundant, environment already contains `hg` annotated with `@[grind _=_]`
-/
#guard_msgs (warning) in
example : True := by grind [=_ hg]

/--
warning: this parameter is redundant, environment already contains `Array.size_set` annotated with `@[grind =]`
-/
#guard_msgs (warning) in
example : True := by grind [= Array.size_set]

#guard_msgs (warning) in
example : True := by grind [pqf]

/--
warning: this parameter is redundant, environment already contains `hg` annotated with `@[grind _=_]`
-/
#guard_msgs (warning) in
example : True := by grind [hg]

@[grind =] theorem mem_range : m ∈ List.range n ↔ m < n :=
  sorry

/--
warning: this parameter is redundant, environment already contains `mem_range` annotated with `@[grind =]`
-/
#guard_msgs (warning) in
example : True := by grind [mem_range]

/--
warning: this parameter is redundant, environment already contains `mem_range` annotated with `@[grind =]`
-/
#guard_msgs (warning) in
example : True := by grind [= mem_range]
