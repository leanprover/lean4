import Module.Basic
import Lean

/-- info: @[defeq] theorem f.eq_def : f = 1 -/
#guard_msgs in #print sig f.eq_def

/-- info: @[defeq] theorem f.eq_unfold : f = 1 -/
#guard_msgs in #print sig f.eq_unfold

/-- info: @[defeq] theorem f_struct.eq_1 : f_struct 0 = 0 -/
#guard_msgs in #print sig f_struct.eq_1
/--
info: theorem f_struct.eq_def : ∀ (x : Nat),
  f_struct x =
    match x with
    | 0 => 0
    | n.succ => f_struct n
-/
#guard_msgs in #print sig f_struct.eq_def

/--
info: theorem f_struct.eq_unfold : f_struct = fun x =>
  match x with
  | 0 => 0
  | n.succ => f_struct n
-/
#guard_msgs in #print sig f_struct.eq_unfold

/-- info: theorem f_wfrec.eq_1 : ∀ (x : Nat), f_wfrec 0 x = x -/
#guard_msgs(pass trace, all) in #print sig f_wfrec.eq_1

/--
info: theorem f_wfrec.eq_def : ∀ (x x_1 : Nat),
  f_wfrec x x_1 =
    match x, x_1 with
    | 0, acc => acc
    | n.succ, acc => f_wfrec n (acc + 1)
-/
#guard_msgs(pass trace, all) in #print sig f_wfrec.eq_def

/--
info: theorem f_wfrec.eq_unfold : f_wfrec = fun x x_1 =>
  match x, x_1 with
  | 0, acc => acc
  | n.succ, acc => f_wfrec n (acc + 1)
-/
#guard_msgs(pass trace, all) in #print sig f_wfrec.eq_unfold

/--
info: theorem f_wfrec.induct_unfolding : ∀ (motive : Nat → Nat → Nat → Prop),
  (∀ (acc : Nat), motive 0 acc acc) →
    (∀ (n acc : Nat), motive n (acc + 1) (f_wfrec n (acc + 1)) → motive n.succ acc (f_wfrec n (acc + 1))) →
      ∀ (a a_1 : Nat), motive a a_1 (f_wfrec a a_1)
-/
#guard_msgs(pass trace, all) in #print sig f_wfrec.induct_unfolding

/-- info: theorem f_exp_wfrec.eq_1 : ∀ (x : Nat), f_exp_wfrec 0 x = x -/
#guard_msgs(pass trace, all) in
#print sig f_exp_wfrec.eq_1

/--
info: theorem f_exp_wfrec.eq_def : ∀ (x x_1 : Nat),
  f_exp_wfrec x x_1 =
    match x, x_1 with
    | 0, acc => acc
    | n.succ, acc => f_exp_wfrec n (acc + 1)
-/
#guard_msgs in #print sig f_exp_wfrec.eq_def

/--
info: theorem f_exp_wfrec.eq_unfold : f_exp_wfrec = fun x x_1 =>
  match x, x_1 with
  | 0, acc => acc
  | n.succ, acc => f_exp_wfrec n (acc + 1)
-/
#guard_msgs(pass trace, all) in #print sig f_exp_wfrec.eq_unfold

/--
info: theorem f_exp_wfrec.induct_unfolding : ∀ (motive : Nat → Nat → Nat → Prop),
  (∀ (acc : Nat), motive 0 acc acc) →
    (∀ (n acc : Nat), motive n (acc + 1) (f_exp_wfrec n (acc + 1)) → motive n.succ acc (f_exp_wfrec n (acc + 1))) →
      ∀ (a a_1 : Nat), motive a a_1 (f_exp_wfrec a a_1)
-/
#guard_msgs(pass trace, all) in #print sig f_exp_wfrec.induct_unfolding
