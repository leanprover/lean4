module

prelude
import Module.Basic

/-! Theorems should be exported without their bodies -/

/--
info: theorem t : f = 1 :=
<not imported>
-/
#guard_msgs in
#print t

/-- error: dsimp made no progress -/
#guard_msgs in
example : f = 1 := by dsimp only [t]

example : t = t := by dsimp only [trfl]

/--
error: invalid field 'eq_def', the environment does not contain 'Nat.eq_def'
  f
has type
  Nat
-/
#guard_msgs in
#check f.eq_def

/--
error: invalid field 'eq_unfold', the environment does not contain 'Nat.eq_unfold'
  f
has type
  Nat
-/
#guard_msgs in
#check f.eq_unfold

/-- error: unknown constant 'f_struct.eq_1' -/
#guard_msgs in
#check f_struct.eq_1

/-- error: unknown constant 'f_struct.eq_def' -/
#guard_msgs in
#check f_struct.eq_def

/-- error: unknown constant 'f_struct.eq_unfold' -/
#guard_msgs in
#check f_struct.eq_unfold

/-- error: unknown constant 'f_wfrec.eq_1' -/
#guard_msgs in
#check f_wfrec.eq_1

/-- error: unknown constant 'f_wfrec.eq_def' -/
#guard_msgs in
#check f_wfrec.eq_def

/-- error: unknown constant 'f_wfrec.eq_unfold' -/
#guard_msgs in
#check f_wfrec.eq_unfold

/-- info: f_exp_wfrec.eq_1 : f_exp_wfrec 0 = 0 -/
#guard_msgs in
#check f_exp_wfrec.eq_1

/--
info: f_exp_wfrec.eq_def (x✝ : Nat) :
  f_exp_wfrec x✝ =
    match x✝ with
    | 0 => 0
    | n.succ => f_exp_wfrec n
-/
#guard_msgs in
#check f_exp_wfrec.eq_def

/--
info: f_exp_wfrec.eq_unfold :
  f_exp_wfrec = fun x =>
    match x with
    | 0 => 0
    | n.succ => f_exp_wfrec n
-/
#guard_msgs in
#check f_exp_wfrec.eq_unfold
