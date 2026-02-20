/-!
# Test for issue 6373, variable capture for app elaborator eta feature

https://github.com/leanprover/lean4/issues/6373
-/

def sum3 (x y z : Nat) : Nat := x + y + z

/-!
The following two used to elaborate differently.
Now in the second, we can see that the `x` in the `fun` (from the eta feature), does not shadow the `x` in the `let`.
Note that in both, `y` can still be used as a named argument.
-/
/--
info: fun x =>
  (let w := 15;
    fun x y => sum3 x y w)
    x 3 : Nat → Nat
-/
#guard_msgs in
#check (let w := 15; sum3 (z := w)) (y := 3)
/--
info: fun x =>
  (let x := 15;
    fun x_1 y => sum3 x_1 y x)
    x 3 : Nat → Nat
-/
#guard_msgs in
#check (let x := 15; sum3 (z := x)) (y := 3)

/-!
Verifying that each evaluates to the same value when evaluated at `0`.
The second used to evaluate to `3` instead of `18`.
-/
/-- info: 18 -/
#guard_msgs in
#eval (let w := 15; sum3 (z := w)) (y := 3) <| 0
/-- info: 18 -/
#guard_msgs in
#eval (let x := 15; sum3 (z := x)) (y := 3) <| 0

/-!
Same verification, but make sure that `0` can be passed as a named argument.
-/
/-- info: 18 -/
#guard_msgs in
#eval (let w := 15; sum3 (z := w)) (y := 3) (x := 0)
/-- info: 18 -/
#guard_msgs in
#eval (let x := 15; sum3 (z := x)) (y := 3) (x := 0)
