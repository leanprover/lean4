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
/-- info: Bool.f a : Bool -/
#guard_msgs in #check a.f

-- Semireducible definitions are not unfolded however.
def semifriend (α : Type) [Friend α] := Friend.friend α

def _root_.Bool.g (b : semifriend Nat) := !b

/--
error: invalid field notation, function 'Bool.g' does not have argument with type (Bool ...) that can be used, it must be explicit or implicit with a unique name
-/
#guard_msgs in #check a.g

end Ex2
