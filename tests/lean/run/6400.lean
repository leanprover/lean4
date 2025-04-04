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
