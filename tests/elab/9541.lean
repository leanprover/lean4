/-!
# DecidableEq deriving handler for enumerations in higher universes

https://github.com/leanprover/lean4/issues/9541
-/

/-!
Basic case, this always worked.
-/
inductive I0 : Type
  | A | B | C
  deriving DecidableEq

/-!
Example from the issue.
-/
inductive I1 : Type 1
  | A | B | C
  deriving DecidableEq

/-!
Parameterized works.
-/
inductive I2.{u} : Type u
  | A | B | C
  deriving DecidableEq

/-!
Parameterized with two variables works.
-/
inductive I3.{u, v} : Type (max u v)
  | A | B | C
  deriving DecidableEq

/-!
Parameterized with `Sort (max 1 _)` works.
-/
inductive I4.{u} : Sort (max 1 u)
  | A | B | C
  deriving DecidableEq

/-- info: instDecidableEqI4 -/
#guard_msgs in #synth DecidableEq I4.{0}
/-- info: instDecidableEqI4 -/
#guard_msgs in #synth DecidableEq I4.{1}
