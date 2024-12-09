
/-!
This test checks if the functional induction principle has fewer universe parameters
if the original function has a parameter that disappears.
-/

namespace Structural
def foo.{u} : Nat → PUnit.{u}
| 0 => .unit
| n+1 => foo n

/--
info: Structural.foo.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : ∀ (n : Nat), motive n → motive n.succ)
  (a✝ : Nat) : motive a✝
-/
#guard_msgs in
#check foo.induct

example : foo n = .unit := by
  induction n using foo.induct with
  | case1 => unfold foo; rfl
  | case2 n ih => unfold foo; exact ih

end Structural

namespace WellFounded
def foo.{u,v} {α : Type v} : List α  → PUnit.{u}
| [] => .unit
| _ :: xs => foo xs
termination_by xs => xs

/--
info: WellFounded.foo.induct.{v} {α : Type v} (motive : List α → Prop) (case1 : motive [])
  (case2 : ∀ (head : α) (xs : List α), motive xs → motive (head :: xs)) (a✝ : List α) : motive a✝
-/
#guard_msgs in
#check foo.induct

example : foo xs = .unit := by
  induction xs using foo.induct with
  | case1 => unfold foo; rfl
  | case2 _ xs ih => unfold foo; exact ih

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

/--
info: Mutual.foo.induct (motive1 motive2 : Nat → Prop) (case1 : motive1 0) (case2 : ∀ (n : Nat), motive2 n → motive1 n.succ)
  (case3 : motive2 0) (case4 : ∀ (n : Nat), motive1 n → motive2 n.succ) (a✝ : Nat) : motive1 a✝
-/
#guard_msgs in
#check foo.induct

example : foo n = .unit := by
  induction n using foo.induct (motive2 := fun n => bar n = .unit) with
  | case1 => unfold foo; rfl
  | case2 n ih => unfold foo; exact ih
  | case3 => unfold bar; rfl
  | case4 n ih => unfold bar; exact ih

end Mutual
