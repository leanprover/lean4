/-!
Checks that `simp` removes the `binderNameHint` in the pre-phase, and does not spend time looking
at its arguments.

The following traces should show no rewriting of `x` or `y`, only `z`.
-/

def x : Nat := 0
def y : Nat := 0
def z : Nat := 0

set_option trace.Meta.Tactic.simp.rewrite true

/--
info: [Meta.Tactic.simp.rewrite] ↓ binderNameHint.eq_1:1000:
      binderNameHint x y z
    ==>
      z
[Meta.Tactic.simp.rewrite] unfold z, z ==> 0
[Meta.Tactic.simp.rewrite] eq_self:1000: 0 = 0 ==> True
-/
#guard_msgs in
example : binderNameHint x y z = 0 := by
  simp [x, y, z]

/--
info: [Meta.Tactic.simp.rewrite] ↓ binderNameHint.eq_1:1000:
      binderNameHint x y z
    ==>
      z
[Meta.Tactic.simp.rewrite] unfold z, z ==> 0
-/
#guard_msgs in
example : binderNameHint x y z = 0 := by
  dsimp [x, y, z]
