module

prelude
public import all Module.Basic

/-! `import all` should import private information, privately. -/

/--
info: theorem t : f = 1 :=
testSorry
-/
#guard_msgs in
#print t

/--
error: type mismatch
  y
has type
  Vector Unit 1
but is expected to have type
  Vector Unit f
-/
#guard_msgs in
public theorem v (x : Vector Unit f) (y : Vector Unit 1) : x = y := sorry

/-- error: dsimp made no progress -/
#guard_msgs in
example : P f := by dsimp only [t]; exact hP1
example : P f := by simp only [t]; exact hP1

/-- error: dsimp made no progress -/
#guard_msgs in
example : P f := by dsimp only [trfl]; exact hP1
/-- error: dsimp made no progress -/
#guard_msgs in
example : P f := by dsimp only [trfl']; exact hP1

example : P f := by dsimp only [trflprivate]; exact hP1
example : P f := by dsimp only [trflprivate']; exact hP1


example : P fexp := by dsimp only [fexp_trfl]; exact hP1
example : P fexp := by dsimp only [fexp_trfl']; exact hP1


/-- info: @[defeq] private theorem f.eq_def : f = 1 -/
#guard_msgs in #print sig f.eq_def

/-- info: @[defeq] private theorem f.eq_unfold : f = 1 -/
#guard_msgs in #print sig f.eq_unfold

/-- info: @[defeq] private theorem f_struct.eq_1 : f_struct 0 = 0 -/
#guard_msgs in #print sig f_struct.eq_1

/--
info: private theorem f_struct.eq_def : ∀ (x : Nat),
  f_struct x =
    match x with
    | 0 => 0
    | n.succ => f_struct n
-/
#guard_msgs in #print sig f_struct.eq_def

/--
info: private theorem f_struct.eq_unfold : f_struct = fun x =>
  match x with
  | 0 => 0
  | n.succ => f_struct n
-/
#guard_msgs in #print sig f_struct.eq_unfold

/-- info: private theorem f_wfrec.eq_1 : ∀ (x : Nat), f_wfrec 0 x = x -/
#guard_msgs(pass trace, all) in #print sig f_wfrec.eq_1

/--
info: private theorem f_wfrec.eq_def : ∀ (x x_1 : Nat),
  f_wfrec x x_1 =
    match x, x_1 with
    | 0, acc => acc
    | n.succ, acc => f_wfrec n (acc + 1)
-/
#guard_msgs(pass trace, all) in #print sig f_wfrec.eq_def

/--
info: private theorem f_wfrec.eq_unfold : f_wfrec = fun x x_1 =>
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
#guard_msgs in #print sig f_exp_wfrec.eq_1

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
#guard_msgs in #print sig f_exp_wfrec.eq_unfold

/--
info: theorem f_exp_wfrec.induct_unfolding : ∀ (motive : Nat → Nat → Nat → Prop),
  (∀ (acc : Nat), motive 0 acc acc) →
    (∀ (n acc : Nat), motive n (acc + 1) (f_exp_wfrec n (acc + 1)) → motive n.succ acc (f_exp_wfrec n (acc + 1))) →
      ∀ (a a_1 : Nat), motive a a_1 (f_exp_wfrec a a_1)
-/
#guard_msgs(pass trace, all) in #print sig f_exp_wfrec.induct_unfolding

/-! `import all` should allow access to private defs, privately. -/

public def pub := priv

/-- error: unknown identifier 'priv' -/
#guard_msgs in
@[expose] public def pub' := priv
