@[irreducible] def f (x : Nat) := x + 1
set_option allowUnsafeReducibility true
set_option pp.mvars false
/--
error: Type mismatch
  rfl
has type
  ?_ = ?_
but is expected to have type
  f x = x + 1
-/
#guard_msgs in
example : f x = x + 1 :=
  rfl

section
  attribute [local reducible] f
  example : f x = x + 1 :=
    rfl
end

/--
error: Type mismatch
  rfl
has type
  ?_ = ?_
but is expected to have type
  f x = x + 1
-/
#guard_msgs in
example : f x = x + 1 :=
  rfl

namespace Boo
  attribute [scoped semireducible] f
end Boo

/--
error: Type mismatch
  rfl
has type
  ?_ = ?_
but is expected to have type
  f x = x + 1
-/
#guard_msgs in
example : f x = x + 1 :=
  rfl

open Boo in -- `f` should be `semireducible
example : f x = x + 1 :=
  rfl

/--
error: Type mismatch
  rfl
has type
  ?_ = ?_
but is expected to have type
  f x = x + 1
-/
#guard_msgs in
example : f x = x + 1 :=
  rfl
