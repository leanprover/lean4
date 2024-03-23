
/-!
This test checks if the functional induction principle has fewer universe parameters
if the original function has a parameter that disappears.
-/

namespace Structural
def foo.{u} : Nat → PUnit.{u}
| 0 => .unit
| n+1 => foo n

derive_functional_induction foo

example : foo n = .unit := by
  induction n using foo.induct with
  | case1 => unfold foo; rfl
  | case2 n ih => unfold foo; exact ih

end Structural

namespace WellFounded
def foo.{u} : Nat → PUnit.{u}
| 0 => .unit
| n+1 => foo n
termination_by n => n

derive_functional_induction foo

example : foo n = .unit := by
  induction n using foo.induct with
  | case1 => unfold foo; rfl
  | case2 n ih => unfold foo; exact ih

end WellFounded


namespace Mutual
mutual
def foo.{u} : Nat → PUnit.{u}
| 0 => .unit
| n+1 => bar n
termination_by n => n
def bar.{u} : Nat → PUnit.{u}
| 0 => .unit
| n+1 => foo n
termination_by n => n
end

derive_functional_induction foo

example : foo n = .unit := by
  induction n using foo.induct (motive2 := fun n => bar n = .unit) with
  | case1 => unfold foo; rfl
  | case2 => unfold bar; rfl
  | case3 n ih => unfold foo; exact ih
  | case4 n ih => unfold bar; exact ih

end Mutual
