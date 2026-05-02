set_option grind.ematch.diagnostics true
set_option warn.sorry false

opaque p1 : Nat → Prop
opaque p2 : Nat → Prop
opaque p3 : Nat → Prop
opaque p4 : Nat → Prop
opaque p5 : Nat → Prop
opaque p6 : Nat → Prop

@[grind →] theorem th1 {x} : p1 x → p2 x := sorry
@[grind →] theorem th2 {x} : p2 x → p3 x := sorry
@[grind →] theorem th3 {x} : p2 x → p4 x := sorry

theorem th4 {x} : p3 x → p4 x → p5 x := sorry
grind_pattern th4 => p3 x, p4 x

@[grind →] theorem th5 {x} : p5 x → p6 x := sorry

set_option trace.grind.ematch.diagnostics.compact true

/--
trace: [grind.ematch.diagnostics.compact] ✅️ instances
  [inst] [] => th1
  [inst] [th1] => th3
  [inst] [th1] => th2
  [inst] [th2, th3] => th4
  [inst] [th4] => th5
-/
#guard_msgs in
example : p1 a → p6 a := by
  grind
