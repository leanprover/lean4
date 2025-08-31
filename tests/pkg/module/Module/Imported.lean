module

prelude
public import Module.Basic

/-! Definitions should be exported without their bodies by default -/

/--
info: def f : Nat :=
<not imported>
-/
#guard_msgs in
#print f

/-! Theorems should be exported without their bodies -/

/--
info: theorem t : f = 1 :=
<not imported>
-/
#guard_msgs in
#print t

/--
info: theorem trfl : f = 1 :=
<not imported>
-/
#guard_msgs in
#print trfl

/-! Metadata of private decls should not be exported. -/

-- Should not fail with 'unknown constant `inst*`
/--
error: failed to synthesize
  X

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
def fX : X := inferInstance

/-- error: `dsimp` made no progress -/
#guard_msgs in
example : P f := by dsimp only [t]; exact hP1
example : P f := by simp only [t]; exact hP1

/-- error: `dsimp` made no progress -/
#guard_msgs in
example : P f := by dsimp only [trfl]; exact hP1
/-- error: `dsimp` made no progress -/
#guard_msgs in
example : P f := by dsimp only [trfl']; exact hP1

example : P fexp := by dsimp only [fexp_trfl]; exact hP1
example : P fexp := by dsimp only [fexp_trfl']; exact hP1
example : t = t := by dsimp only [trfl]

/--
error: Invalid field `eq_def`: The environment does not contain `Nat.eq_def`
  f
has type
  Nat
-/
#guard_msgs in
#check f.eq_def

/--
error: Invalid field `eq_unfold`: The environment does not contain `Nat.eq_unfold`
  f
has type
  Nat
-/
#guard_msgs in
#check f.eq_unfold

/-- error: Unknown constant `f_struct.eq_1` -/
#guard_msgs in
#check f_struct.eq_1

/-- error: Unknown constant `f_struct.eq_def` -/
#guard_msgs in
#check f_struct.eq_def

/-- error: Unknown constant `f_struct.eq_unfold` -/
#guard_msgs in
#check f_struct.eq_unfold

/-- error: Unknown constant `f_wfrec.eq_1` -/
#guard_msgs in
#check f_wfrec.eq_1

/-- error: Unknown constant `f_wfrec.eq_def` -/
#guard_msgs in
#check f_wfrec.eq_def

/-- error: Unknown constant `f_wfrec.eq_unfold` -/
#guard_msgs in
#check f_wfrec.eq_unfold

/-- error: Unknown constant `f_wfrec.induct_unfolding` -/
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
