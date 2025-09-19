reset_grind_attrs%

def succ (x : Nat) := x+1

/-- trace: [grind.inj] succ_inj: [succ] -/
#guard_msgs in
set_option trace.grind.inj true in
@[grind inj] theorem succ_inj : Function.Injective succ := by
  grind [Function.Injective, succ]

/-- trace: [grind.debug.inj] [succ_inj] -/
#guard_msgs in
example : True := by
  set_option trace.grind.debug.inj true in
  grind

/-- trace: [grind.debug.inj] [] -/
#guard_msgs in
example : True := by
  set_option trace.grind.debug.inj true in
  grind [- succ_inj]

def double (x : Nat) := 2*x

@[grind inj] theorem double_inj : Function.Injective double := by
  grind [Function.Injective, double]

/-- trace: [grind.debug.inj] [double_inj, succ_inj] -/
#guard_msgs in
example : True := by
  set_option trace.grind.debug.inj true in
  grind

attribute [- grind] succ_inj

/-- error: `succ_inj` is not marked with the `[grind]` attribute -/
#guard_msgs in
example : True := by
  grind [- succ_inj]

/--
error: invalid `[grind inj]` theorem, resulting type is not of the form `Function.Injective <fun>`
  x = y
-/
#guard_msgs in
@[grind inj] theorem succ_inj' : succ x = succ y → x = y := by
  grind [succ]
