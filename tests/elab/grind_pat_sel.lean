-- Enable new pattern selection algorithm
set_option backward.grind.inferPattern false
set_option warn.sorry false

opaque f : Nat → Nat
opaque g : Nat → Nat

/-- info: fg₁: [g #0] -/
#guard_msgs in
@[grind!? ←] axiom fg₁ : f (g x) = x

set_option trace.Meta.debug true

/-- info: fg₂: [f (g #0)] -/
#guard_msgs in
@[grind? ←] axiom fg₂ : f (g x) = x

/-- error: redundant modifier `!` in `grind` attribute -/
#guard_msgs in
@[grind! =] axiom fg₃ : f (g x) = x

/-- error: redundant modifier `!` in `grind` attribute -/
#guard_msgs in
@[grind! =_] axiom fg₄ : f (g x) = x

/--
error: invalid pattern, (non-forbidden) application expected
  #0
-/
#guard_msgs (error) in
@[grind =_] theorem fg₅ : f (g x) = x := sorry

opaque p : Nat → Prop

/-- info: pf₁: [f #3, f #2] -/
#guard_msgs in
@[grind!? →] axiom pf₁ : p (f x) → p (f y) → f x = f y

/-- info: pf₂: [p (f #3), p (f #2)] -/
#guard_msgs in
@[grind? →] axiom pf₂ : p (f x) → p (f y) → f x = f y

/-- info: pf₃: [p (f #3), f (f #2)] -/
#guard_msgs in
@[grind? →] axiom pf₃ : p (f x) → f (f y) = y → f x = f y

opaque r : Nat → Nat → Nat

/-- info: pr₁: [p (f #2), r #2 (f #1)] -/
#guard_msgs in
@[grind? =>] axiom pr₁ : p (f x) → r x (f y) = y

/-- info: pr₂: [f #2, f #1] -/
#guard_msgs in
@[grind!? =>] axiom pr₂ : p (f x) → r x (f y) = y

/-- info: pr₃: [r #2 (f #1)] -/
#guard_msgs in
@[grind!? <=] axiom pr₃ : p (f x) → r x (f y) = y

/-- info: pr₄: [r #1 (f #1), p (f #2)] -/
#guard_msgs in
@[grind? <=] axiom pr₄ : p (f x) → r y (f y) = y

/--
info: Try these:
  [apply] [grind! .] for pattern: [r #2 (f #1)]
  [apply] [grind! =>] for pattern: [f #2, f #1]
-/
#guard_msgs in
@[grind!] theorem pr₅ : p (f x) → r x (f y) = y := sorry

/--
info: Try these:
  [apply] [grind! .] for pattern: [f #1, f #2]
  [apply] [grind! =>] for pattern: [f #2, f #1]
-/
#guard_msgs in
@[grind!] theorem pr₆ : p (f x) → r y (f y) = y := sorry

/--
info: Try these:
  [apply] [grind .] for pattern: [r #1 (f #1), p (f #2)]
  [apply] [grind =>] for pattern: [p (f #2), r #1 (f #1)]
  [apply] [grind! .] for pattern: [f #1, f #2]
  [apply] [grind! =>] for pattern: [f #2, f #1]
-/
#guard_msgs in
@[grind] theorem pr₇ : p (f x) → r y (f y) = y := sorry

/--
info: Try these:
  [apply] [grind =] for pattern: [r #2 (f #1)]
  [apply] [grind =>] for pattern: [p (f #2), r #2 (f #1)]
  [apply] [grind! =>] for pattern: [f #2, f #1]
-/
#guard_msgs in
@[grind] theorem pr₈ : p (f x) → r x (f y) = y := sorry


/--
info: Try these:
  [apply] [grind =] for pattern: [f (g #0)]
  [apply] [grind! .] for pattern: [g #0]
-/
#guard_msgs in
@[grind] axiom fg₆ : f (g x) = x

/--
info: Try these:
  [apply] [grind =] for pattern: [f (g #0)]
  [apply] [grind =_] for pattern: [r #0 #0]
  [apply] [grind! .] for pattern: [g #0]
-/
#guard_msgs in
@[grind] axiom fg₇ : f (g x) = r x x

/--
info: Try this:
  [apply] [grind =] for pattern: [f #0]
-/
#guard_msgs in
@[grind] axiom fg₈ : f x = x

namespace Foo

opaque foo : Nat → Nat
opaque fooInv : Nat → Nat
axiom fooInv_foo : fooInv (foo x) = x

/-- trace: [grind.ematch.pattern] fooInv_foo: [foo #0] -/
#guard_msgs in
set_option trace.grind.ematch.pattern true in
example : foo x = foo y → x = y := by
  grind [!←fooInv_foo]

/-- trace: [grind.ematch.pattern] fooInv_foo: [fooInv (foo #0)] -/
#guard_msgs in
set_option trace.grind.ematch.pattern true in
example : foo x = foo y → x = y := by
  fail_if_success grind [←fooInv_foo]
  sorry

opaque bar : Nat → Nat
axiom bar_eq : bar x = foo x

/-- error: redundant modifier `!` in `grind` parameter -/
#guard_msgs in
example : bar x = bar y → x = y := by
  grind [! = bar_eq]

/-- error: redundant modifier `!` in `grind` parameter -/
#guard_msgs in
example : bar x = bar y → x = y := by
  grind [! =_ bar_eq]

/-- error: redundant modifier `!` in `grind` parameter -/
#guard_msgs in
example : bar x = bar y → x = y := by
  grind [! _=_ bar_eq]

end Foo
