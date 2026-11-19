def t : True := by simp

/--
error: Despite the `in`, the attribute irreducible is added globally to t
please remove the `in` or make this a `local irreducible`
-/
#guard_msgs in
attribute [local simp, irreducible] t in
example : True := t

/--
error: Despite the `in`, the attribute simp is added globally to t
please remove the `in` or make this a `local simp`
-/
#guard_msgs in
attribute [simp] t in
example : True := t

def t' : True := by simp

/--
error: Despite the `in`, the attribute simp is added globally to t'
please remove the `in` or make this a `local simp`
---
error: Despite the `in`, the attribute irreducible is added globally to t'
please remove the `in` or make this a `local irreducible`
-/
#guard_msgs in
attribute [simp, irreducible] t' in
example : True := t'

attribute [local simp] t in
example : True := t

section
/--
error: Despite the `in`, the attribute simp is added globally to t
please remove the `in` or make this a `local simp`
-/
#guard_msgs in
attribute [simp] t in
example : True := t
end

/--
error: Despite the `in`, the attribute simp is added globally to t
please remove the `in` or make this a `local simp`
---
error: Despite the `in`, the attribute simp is added globally to t'
please remove the `in` or make this a `local simp`
-/
#guard_msgs in
attribute [simp] t in
set_option trace.Meta.Tactic true in
attribute [simp] t' in
example : True := t
