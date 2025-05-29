import Module.Basic
import Lean

/-- info: f.eq_def : f = 1 -/
#guard_msgs in
#check f.eq_def

/-- info: f.eq_unfold : f = 1 -/
#guard_msgs in
#check f.eq_unfold

/-- info: f_struct.eq_1 : f_struct 0 = 0 -/
#guard_msgs in
#check f_struct.eq_1

/--
info: f_struct.eq_def (x✝ : Nat) :
  f_struct x✝ =
    match x✝ with
    | 0 => 0
    | n.succ => f_struct n
-/
#guard_msgs in
#check f_struct.eq_def

/--
info: f_struct.eq_unfold :
  f_struct = fun x =>
    match x with
    | 0 => 0
    | n.succ => f_struct n
-/
#guard_msgs in
#check f_struct.eq_unfold

/-- info: f_wfrec.eq_1 : f_wfrec 0 = 0 -/
#guard_msgs(pass trace, all) in
#check f_wfrec.eq_1

/--
info: f_wfrec.eq_def (x✝ : Nat) :
  f_wfrec x✝ =
    match x✝ with
    | 0 => 0
    | n.succ => f_wfrec n
-/
#guard_msgs(pass trace, all) in
#check f_wfrec.eq_def

/--
info: f_wfrec.eq_unfold :
  f_wfrec = fun x =>
    match x with
    | 0 => 0
    | n.succ => f_wfrec n
-/
#guard_msgs(pass trace, all) in
#check f_wfrec.eq_unfold

/-- info: f_exp_wfrec.eq_1 : f_exp_wfrec 0 = 0 -/
#guard_msgs(pass trace, all) in
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
#guard_msgs(pass trace, all) in
#check f_exp_wfrec.eq_unfold
