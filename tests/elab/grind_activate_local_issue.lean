module
opaque p : Nat → Prop

-- Local forall should be activated only once
/-- trace: [grind.ematch] activated `h`, [p #0] -/
#guard_msgs in
example : (∀ x, p x) → p (x + 2) := by
  set_option trace.grind.ematch true in
  grind
