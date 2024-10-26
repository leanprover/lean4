/-!
# Tests of `addPPExplicitToExposeDiff`
-/
set_option pp.mvars false

/-!
Does discretionary metavariable assignments so that we can see where the difference really was.
In the following, `this` actually has type `?m = 3`.
-/
/--
error: type mismatch
  this
has type
  1 = 3 : Prop
but is expected to have type
  1 = 2 : Prop
---
error: unsolved goals
⊢ 1 = 3
-/
#guard_msgs in example : 1 = 2 := by
  change _ = 3


/-!
Error message shouldn't fake a higher order unification. This next one used to give
```
  type mismatch
    test n2 ?m.648
  has type
    (fun x ↦ x * 2) (g2 n2) = n2 : Prop
  but is expected to have type
    (fun x ↦ x * 2) (g2 n2) = n2 : Prop
```
-/

theorem test {f g : Nat → Nat} (n : Nat) (hfg : ∀ a, f (g a) = a) :
    f (g n) = n := hfg n

/--
error: type mismatch
  test n2 ?_
has type
  ?_ (?_ n2) = n2 : Prop
but is expected to have type
  (fun x => x * 2) (g2 n2) = n2 : Prop
-/
#guard_msgs in
example {g2 : Nat → Nat} (n2 : Nat) : (fun x => x * 2) (g2 n2) = n2 := by
  with_reducible refine test n2 ?_
