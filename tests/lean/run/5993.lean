/-!
# Avoid delaborating with field notation if object is a metavariable application.

https://github.com/leanprover/lean4/issues/5993
-/

set_option pp.mvars false

/-!
No field notation notation here. Used to print `refine ?_.succ` and `refine ?_.snd`.
-/

/--
info: Try this: refine Nat.succ ?_
---
info: Try this: refine Prod.snd ?_
-/
#guard_msgs in
example : Nat := by
  show_term refine Nat.succ ?_
  show_term refine Prod.snd (α := Int) ?_
  exact default

/-!
No field notation even under binders. (That is, be aware of delayed assignment metavariables.)
-/

/-- info: Try this: refine fun x => Nat.succ ?_ -/
#guard_msgs in
example : Nat → Nat := by
  show_term refine fun _ => Nat.succ ?_
  exact default
