module

prelude
import all Module.Basic

/-! `import all` should import private information, privately. -/

/--
info: theorem t : f = 1 :=
sorry
-/
#guard_msgs in
#print t

/--
error: type mismatch
  y
has type
  Vector Unit 1 : Type
but is expected to have type
  Vector Unit f : Type
-/
#guard_msgs in
theorem v (x : Vector Unit f) (y : Vector Unit 1) : x = y := sorry



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

/-- info: f_wfrec.eq_1 (x✝ : Nat) : f_wfrec 0 x✝ = x✝ -/
#guard_msgs(pass trace, all) in
#check f_wfrec.eq_1

/--
info: f_wfrec.eq_def (x✝ x✝¹ : Nat) :
  f_wfrec x✝ x✝¹ =
    match x✝, x✝¹ with
    | 0, acc => acc
    | n.succ, acc => f_wfrec n (acc + 1)
-/
#guard_msgs(pass trace, all) in
#check f_wfrec.eq_def

/--
info: f_wfrec.eq_unfold :
  f_wfrec = fun x x_1 =>
    match x, x_1 with
    | 0, acc => acc
    | n.succ, acc => f_wfrec n (acc + 1)
-/
#guard_msgs(pass trace, all) in
#check f_wfrec.eq_unfold

/--
info: f_wfrec.induct_unfolding (motive : Nat → Nat → Nat → Prop) (case1 : ∀ (acc : Nat), motive 0 acc acc)
  (case2 : ∀ (n acc : Nat), motive n (acc + 1) (f_wfrec n (acc + 1)) → motive n.succ acc (f_wfrec n (acc + 1)))
  (a✝ a✝¹ : Nat) : motive a✝ a✝¹ (f_wfrec a✝ a✝¹)
-/
#guard_msgs(pass trace, all) in
#check f_wfrec.induct_unfolding

/-- info: f_exp_wfrec.eq_1 (x✝ : Nat) : f_exp_wfrec 0 x✝ = x✝ -/
#guard_msgs in
#check f_exp_wfrec.eq_1

/--
info: f_exp_wfrec.eq_def (x✝ x✝¹ : Nat) :
  f_exp_wfrec x✝ x✝¹ =
    match x✝, x✝¹ with
    | 0, acc => acc
    | n.succ, acc => f_exp_wfrec n (acc + 1)
-/
#guard_msgs in
#check f_exp_wfrec.eq_def

/--
info: f_exp_wfrec.eq_unfold :
  f_exp_wfrec = fun x x_1 =>
    match x, x_1 with
    | 0, acc => acc
    | n.succ, acc => f_exp_wfrec n (acc + 1)
-/
#guard_msgs in
#check f_exp_wfrec.eq_unfold

/--
info: f_exp_wfrec.induct_unfolding (motive : Nat → Nat → Nat → Prop) (case1 : ∀ (acc : Nat), motive 0 acc acc)
  (case2 : ∀ (n acc : Nat), motive n (acc + 1) (f_exp_wfrec n (acc + 1)) → motive n.succ acc (f_exp_wfrec n (acc + 1)))
  (a✝ a✝¹ : Nat) : motive a✝ a✝¹ (f_exp_wfrec a✝ a✝¹)
-/
#guard_msgs(pass trace, all) in
#check f_exp_wfrec.induct_unfolding
