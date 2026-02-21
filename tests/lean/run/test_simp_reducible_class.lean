module

/-!
# Test: `simp` with `@[reducible]` class field projections

When a class field like `X.x` is marked `@[reducible]`, `isDefEqDelta` unfolds it to `.proj` form.
`isDefEqProj` must then bump transparency to `.instances` when comparing the struct arguments,
since the projection's parameter is instance-implicit. Without this bump, `eq_self` fails because
instances like `instX a` vs `instX b` are stuck at `.reducible`.
-/

namespace SimpReducibleClassField

@[implicit_reducible] def a := 0
@[implicit_reducible] def b := 0

class X where
  x : Nat

instance instX (n : Nat) : X where
  x := n

-- Test 1: plain simp, semireducible X.x (works on master)
-- isDefEqArgs bumps to .instances for instance-implicit param of X.x
example : (instX a).x = (instX b).x := by simp

-- Test 2: plain simp, @[reducible] X.x (BROKEN on master, fixed by isDefEqProj change)
-- isDefEqDelta unfolds X.x to .proj form, isDefEqProj needs withInstanceConfig
set_option allowUnsafeReducibility true in
attribute [reducible] X.x in
example : (instX a).x = (instX b).x := by simp

-- Test 3: simp [X.x] with semireducible args exposes stuck .proj node
-- reduceProjFn? unfolds X.x at .instances, but the .proj can't reduce further
-- because instX a' is not a constructor app at .reducible. This is expected:
-- the user explicitly requested the unfolding.
def a' := 0
def b' := 0

/--
error: unsolved goals
⊢ (instX a').1 = (instX b').1
-/
#guard_msgs in
example : (instX a').x = (instX b').x := by simp [X.x]

end SimpReducibleClassField
