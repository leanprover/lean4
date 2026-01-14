/-!
# Tests for delaboration of name literals
-/

/-!
Basic constructors
-/

/-- info: `a : Lean.Name -/
#guard_msgs in #check Lean.Name.str Lean.Name.anonymous "a"
/-- info: `a.b : Lean.Name -/
#guard_msgs in #check Lean.Name.str (Lean.Name.str Lean.Name.anonymous "a") "b"

/-!
Alternative constructors
-/

/-- info: `a : Lean.Name -/
#guard_msgs in #check Lean.Name.mkStr1 "a"
/-- info: `a.b : Lean.Name -/
#guard_msgs in #check Lean.Name.mkStr2 "a" "b"
/-- info: `a.b.c : Lean.Name -/
#guard_msgs in #check Lean.Name.mkStr3 "a" "b" "c"
/-- info: `a.b.c.d : Lean.Name -/
#guard_msgs in #check Lean.Name.mkStr4 "a" "b" "c" "d"
/-- info: `a.b.c.d.e : Lean.Name -/
#guard_msgs in #check Lean.Name.mkStr5 "a" "b" "c" "d" "e"
/-- info: `a.b.c.d.e.f : Lean.Name -/
#guard_msgs in #check Lean.Name.mkStr6 "a" "b" "c" "d" "e" "f"
/-- info: `a.b.c.d.e.f.g : Lean.Name -/
#guard_msgs in #check Lean.Name.mkStr7 "a" "b" "c" "d" "e" "f" "g"
/-- info: `a.b.c.d.e.f.g.h : Lean.Name -/
#guard_msgs in #check Lean.Name.mkStr8 "a" "b" "c" "d" "e" "f" "g" "h"

/-!
Combined constructor/alternative
-/

/-- info: `a.b.c : Lean.Name -/
#guard_msgs in #check Lean.Name.str (Lean.Name.mkStr2 "a" "b") "c"

/-!
Escaping
-/

/-- info: `«a.b».«c.d» : Lean.Name -/
#guard_msgs in #check Lean.Name.str (Lean.Name.str Lean.Name.anonymous "a.b") "c.d"

/-- info: `«a.b».«c.d».«e.f» : Lean.Name -/
#guard_msgs in #check Lean.Name.mkStr3 "a.b" "c.d" "e.f"

-- No need to escape `forall` since it can't be a keyword
/-- info: `forall : Lean.Name -/
#guard_msgs in #check Lean.Name.str Lean.Name.anonymous "forall"
