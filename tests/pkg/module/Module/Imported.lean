module

prelude
public import Module.Basic
import Lean.DocString
meta import Lean.Elab.Command

/-! Definitions should be exported without their bodies by default -/

/--
info: def f : Nat :=
<not imported>
-/
#guard_msgs in
#print f

/--
error: Type mismatch
  rfl
has type
  ?m.5 = ?m.5
but is expected to have type
  f = 1

Note: The following definitions were not unfolded because their definition is not exposed:
  f ↦ 1
-/
#guard_msgs in
example : f = 1 := rfl

/--
error: Tactic `apply` failed: could not unify the conclusion of `@rfl`
  ?a = ?a
with the goal
  f = 1

Note: The full type of `@rfl` is
  ∀ {α : Sort ?u.121} {a : α}, a = a

Note: The following definitions were not unfolded because their definition is not exposed:
  f ↦ 1

⊢ f = 1
-/
#guard_msgs in
example : f = 1 := by apply rfl

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
error: failed to synthesize instance of type class
  X

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
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
error: Invalid field `eq_def`: The environment does not contain `Nat.eq_def`, so it is not possible to project the field `eq_def` from an expression
  f
of type `Nat`
-/
#guard_msgs in
#check f.eq_def

/--
error: Invalid field `eq_unfold`: The environment does not contain `Nat.eq_unfold`, so it is not possible to project the field `eq_unfold` from an expression
  f
of type `Nat`
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

/-! Basic non-`meta` check. -/

/-- error: Invalid definition `nonMeta`, may not access declaration `pubMeta` marked as `meta` -/
#guard_msgs in
def nonMeta := pubMeta

/-! `simp` should not pick up inaccessible definitional equations. -/

/-- error: `simp` made no progress -/
#guard_msgs in
theorem f_struct_eq : f_struct 0 = 0 := by
  simp

/-! `[inherit_doc]` should work independently of visibility. -/

/-- info: some "A private definition. " -/
#guard_msgs in
open Lean in
#eval show CoreM _ from do findDocString? (← getEnv) ``pubInheritDoc

/-! Cross-module `meta` checks, including involving compiler-introduced constants. -/

attribute [local delab Nat] delab

/--
error: Cannot add attribute `[Lean.PrettyPrinter.Delaborator.delabAttribute]`: Declaration `noMetaDelab` must be marked as `meta`
-/
#guard_msgs in
attribute [local delab Nat] noMetaDelab

@[noinline] meta def pap (f : α → β) (a : α) : β := f a
public meta def delab' : Lean.PrettyPrinter.Delaborator.Delab :=
  pap delab

-- Used to complain about `_boxed` not being meta
attribute [local delab Nat] delab'

/--
error: Invalid `meta` definition `metaUsingNonMeta`, `f` is not accessible here; consider adding `public meta import Module.Basic`
-/
#guard_msgs in
public meta def metaUsingNonMeta : Nat :=
  f

-- #11672
example : instA = { instA with b := 0 } := rfl
