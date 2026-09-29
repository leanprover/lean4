import Std.WP
import Std.Tactic.Do

/-!
`sym => intro` introduces a binder whose name starts with `__` as an implementation-detail local,
as the elaborator does for such binders, so the goal hides it. `vcgen` introduces the join point
`__do_jp` of a `do` block the same way, so its VCs hide the join point.
-/

/--
trace: case grind
z : Nat
⊢ z = z
-/
#guard_msgs in
example : ∀ __x : Nat, let __y := __x + 1; ∀ z : Nat, z = z := by
  sym =>
    intro __x __y z
    show_goals
    lia

/-! The name passed to `intro` decides, whatever the binder name in the target. -/

/--
trace: case grind
p : Nat → Prop
h : ∀ (n : Nat), p n
⊢ p __x
-/
#guard_msgs in
example (p : Nat → Prop) (h : ∀ n, p n) : ∀ n, p n := by
  sym =>
    intro __x
    show_goals
    apply h __x

/-! Without names, the hygienic name derived from the binder name decides. -/

/--
trace: case grind
z✝ : Nat
⊢ z✝ = z✝
-/
#guard_msgs in
example : ∀ __x : Nat, ∀ z : Nat, z = z := by
  sym =>
    intros
    show_goals
    lia

def f (n : Nat) : Id Nat := do
  let mut x := 0
  if n > 0 then x := 1 else x := 2
  return x + 1

set_option experimental.vcgen true in
/--
trace: case vc1
n : Nat
h✝ : 0 < n
⊢ 1 < 1 + 1
case vc2
n : Nat
h✝ : ¬0 < n
⊢ 1 < 2 + 1
-/
#guard_msgs in
open Std.WP in
example : ⦃ True ⦄ f n ⦃ fun r => r > 1 ⦄ := by
  unfold f
  vcgen
  all_goals trace_state
  all_goals omega
