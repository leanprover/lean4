/-!
# Issue 3745

Field notation for abbreviations would fail if the argument for field notation was an optional parameter.
-/

structure A

abbrev B := A

def A.x (_ : A) := 1
def B.x (_ : B) := 2

def A.y (_ : A) := 1
def B.y (_ : B := {}) := 2

/-!
These were OK before the fix.
-/
/-- info: 1 -/
#guard_msgs in #eval (show A from {}).x
/-- info: 2 -/
#guard_msgs in #eval (show B from {}).x

/-!
The second of these failed before the fix.
-/
/-- info: 1 -/
#guard_msgs in #eval (show A from {}).y
/-- info: 2 -/
#guard_msgs in #eval (show B from {}).y
