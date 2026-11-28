module

public import SplitMod.Basic

public theorem use : 1 < g 3 := g_pos 3

-- A plain import does not see the body of `f`.
/--
error: Type mismatch
  rfl
has type
  ?m.6 = ?m.6
but is expected to have type
  f 0 = 1

Note: The following definitions were not unfolded because their definition is not exposed:
  f ↦ 6
-/
#guard_msgs in
example : f 0 = 1 := rfl
