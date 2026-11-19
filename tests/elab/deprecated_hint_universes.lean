/-!
Tests that the `linter.deprecated` replacement hint is only offered when the replacement binds
the same universe parameters in the same order: explicit universe arguments at the use site are
positional and survive the in-place textual replacement.
-/

set_option linter.deprecated true

def new1.{u,v} : Sort u → Sort v → Nat := fun _ _ => 0

@[deprecated new1 (since:="")]
def old1.{u, v} : Sort u → Sort v → Nat := fun _ _ => 0

/--
warning: `old1` has been deprecated: Use `new1` instead

Hint: Replace the deprecated name:
  o̵l̵d̵n̲e̲w̲1
-/
#guard_msgs in
def test1 : Prop → Type → Nat := old1.{0,1}

def new2.{u,v} : Sort u → Sort v → Nat := fun _ _ => 0

@[deprecated new2 +typeChanged (since:="")]
def old2.{v, u} : Sort u → Sort v → Nat := fun _ _ => 0

/--
warning: `old2` has been deprecated: Use `new2` instead

Note: The updated constant has a different type:
  Sort u → Sort v → Nat
instead of
  Sort u → Sort v → Nat
-/
#guard_msgs in
def test2 : Prop → Type → Nat := old2.{1,0}
