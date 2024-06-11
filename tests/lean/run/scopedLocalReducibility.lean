@[irreducible] def f (x : Nat) := x + 1
set_option allowUnsafeReducibility true
/--
error: type mismatch
  rfl
has type
  f x = f x : Prop
but is expected to have type
  f x = x + 1 : Prop
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
error: type mismatch
  rfl
has type
  f x = f x : Prop
but is expected to have type
  f x = x + 1 : Prop
-/
#guard_msgs in
example : f x = x + 1 :=
  rfl

namespace Boo
  attribute [scoped semireducible] f
end Boo

/--
error: type mismatch
  rfl
has type
  f x = f x : Prop
but is expected to have type
  f x = x + 1 : Prop
-/
#guard_msgs in
example : f x = x + 1 :=
  rfl

open Boo in -- `f` should be `semireducible
example : f x = x + 1 :=
  rfl

/--
error: type mismatch
  rfl
has type
  f x = f x : Prop
but is expected to have type
  f x = x + 1 : Prop
-/
#guard_msgs in
example : f x = x + 1 :=
  rfl
