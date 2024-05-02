def f (x : Nat) := x + 1

/--
error: failed to set `[semireducible]` for `f`, declarations are `[semireducible]` by default
use `set_option allowUnsafeReducibility true` to override reducibility status validation
-/
#guard_msgs in
attribute [semireducible] f

attribute [reducible] f

/--
error: failed to set `[reducible]`, `f` is not currently `[semireducible]`, but `[reducible]`
use `set_option allowUnsafeReducibility true` to override reducibility status validation
-/
#guard_msgs in
attribute [reducible] f -- should fail because of double reducible setting

-- "Reset" `f`
set_option allowUnsafeReducibility true in
attribute [semireducible] f

attribute [irreducible] f

/--
error: failed to set `[irreducible]`, `f` is not currently `[semireducible]`, but `[irreducible]`
use `set_option allowUnsafeReducibility true` to override reducibility status validation
-/
#guard_msgs in
attribute [irreducible] f

attribute [local semireducible] f

/--
error: failed to set `[local semireducible]`, `f` is currently `[semireducible]`, `[irreducible]` expected
use `set_option allowUnsafeReducibility true` to override reducibility status validation
-/
#guard_msgs in
attribute [local semireducible] f

attribute [local irreducible] f

/--
error: failed to set `[local irreducible]`, `f` is currently `[irreducible]`, `[semireducible]` expected
use `set_option allowUnsafeReducibility true` to override reducibility status validation
-/
#guard_msgs in
attribute [local irreducible] f

/--
error: failed to set `[local reducible]` for `f`, recall that `[reducible]` affects the term indexing datastructures used by `simp` and type class resolution
use `set_option allowUnsafeReducibility true` to override reducibility status validation
-/
#guard_msgs in
attribute [local reducible] f

/--
error: failed to set reducibility status, `Nat.add` has not been defined in this file, consider using the `local` modifier
use `set_option allowUnsafeReducibility true` to override reducibility status validation
-/
#guard_msgs in
attribute [semireducible] Nat.add

/--
error: failed to set reducibility status, `Nat.add` has not been defined in this file, consider using the `local` modifier
use `set_option allowUnsafeReducibility true` to override reducibility status validation
-/
#guard_msgs in
attribute [reducible] Nat.add

/--
error: failed to set reducibility status, `Nat.add` has not been defined in this file, consider using the `local` modifier
use `set_option allowUnsafeReducibility true` to override reducibility status validation
-/
#guard_msgs in
attribute [irreducible] Nat.add

/-- error: scoped attributes must be used inside namespaces -/
#guard_msgs in
attribute [scoped reducible] Nat.add

namespace Foo
/--
error: failed to set reducibility status for `Nat.add`, the `scoped` modifier is not recommended for this kind of attribute
use `set_option allowUnsafeReducibility true` to override reducibility status validation
-/
#guard_msgs in
attribute [scoped reducible] Nat.add

set_option allowUnsafeReducibility true in
attribute [scoped reducible] Nat.add

end Foo
