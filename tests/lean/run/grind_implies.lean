set_option trace.grind.eqc true
set_option trace.grind.internalize true

/--
info: [grind.internalize] p → q
[grind.internalize] p
[grind.internalize] q
[grind.eqc] (p → q) = True
[grind.eqc] p = True
[grind.eqc] (p → q) = q
[grind.eqc] q = False
-/
#guard_msgs (info) in
example (p q : Prop) : (p → q) → p → q := by
  grind

/--
info: [grind.internalize] p → q
[grind.internalize] p
[grind.internalize] q
[grind.eqc] (p → q) = True
[grind.eqc] q = False
[grind.eqc] p = False
[grind.eqc] p = True
-/
#guard_msgs (info) in
example (p q : Prop) : (p → q) → ¬q → ¬p := by
  grind

/--
info: [grind.internalize] (p → q) = r
[grind.internalize] Prop
[grind.internalize] p → q
[grind.internalize] p
[grind.internalize] q
[grind.internalize] r
[grind.eqc] ((p → q) = r) = True
[grind.eqc] (p → q) = r
[grind.eqc] p = False
[grind.eqc] (p → q) = True
[grind.eqc] r = False
-/
#guard_msgs (info) in
example (p q : Prop) : (p → q) = r → ¬p → r := by
  grind


/--
info: [grind.internalize] (p → q) = r
[grind.internalize] Prop
[grind.internalize] p → q
[grind.internalize] p
[grind.internalize] q
[grind.internalize] r
[grind.eqc] ((p → q) = r) = True
[grind.eqc] (p → q) = r
[grind.eqc] q = True
[grind.eqc] (p → q) = True
[grind.eqc] r = False
-/
#guard_msgs (info) in
example (p q : Prop) : (p → q) = r → q → r := by
  grind

/--
info: [grind.internalize] (p → q) = r
[grind.internalize] Prop
[grind.internalize] p → q
[grind.internalize] p
[grind.internalize] q
[grind.internalize] r
[grind.eqc] ((p → q) = r) = True
[grind.eqc] (p → q) = r
[grind.eqc] q = False
[grind.eqc] r = True
[grind.eqc] p = False
[grind.eqc] p = True
-/
#guard_msgs (info) in
example (p q : Prop) : (p → q) = r → ¬q → r → ¬p := by
  grind

/--
info: [grind.internalize] (p → q) = r
[grind.internalize] Prop
[grind.internalize] p → q
[grind.internalize] p
[grind.internalize] q
[grind.internalize] r
[grind.eqc] ((p → q) = r) = True
[grind.eqc] (p → q) = r
[grind.eqc] q = False
[grind.eqc] r = False
[grind.eqc] p = True
[grind.eqc] p = False
-/
#guard_msgs (info) in
example (p q : Prop) : (p → q) = r → ¬q → ¬r → p := by
  grind
