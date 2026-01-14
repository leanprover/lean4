/-!
# Tests for issue #6400

https://github.com/leanprover/lean4/issues/6400

Nested field notation was not resolving correctly if there was generalized field notation coming first
and the target wasn't the first explicit argument.
-/

/-!
Example from issue #6400
-/
namespace Ex1

structure S where
  x : Nat

class Class where
  s : S

def Class.foo [c : Class] : S := c.s

-- Always worked
example [c : Class] : S := c.foo
-- Parens made it work
example [c : Class] : Nat := (c.foo).x
-- Formerly, "function expected at Class.foo"
example [c : Class] : Nat := c.foo.x

end Ex1

/-!
Fixed recursive calls too, which had the same problem.
-/
def Nat.f {n : Nat} : Nat :=
  match n with
  | 0 => 0
  | n + 1 => n.f.succ


/-!
Now instances are unfolded when searching for a relevant argument.
-/
namespace Ex2

class Friend (α : Type) where
  friend : Type

instance : Friend Nat where
  friend := Bool

def _root_.Bool.f (b : Friend.friend Nat) := !b

variable (a : Bool)
/-- info: a.f : Bool -/
#guard_msgs in #check a.f

-- Semireducible definitions are not unfolded however.
def semifriend (α : Type) [Friend α] := Friend.friend α

def _root_.Bool.g (b : semifriend Nat) := !b

/--
error: Invalid field notation: Function `Bool.g` does not have a usable parameter of type `Bool` for which to substitute `a`

Note: Such a parameter must be explicit, or implicit with a unique name, to be used by field notation
-/
#guard_msgs in #check a.g

end Ex2
