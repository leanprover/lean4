/-!
`dsimp.resynthInstances` adopts a resynthesized instance when it is defeq to the old one at
`.implicit`, or at `.default` under `backward.isDefEq.respectTransparency false`.

Here `dsimp only [myid]` rewrites the explicit argument `myid x` of `instC`. The resynthesized
`instC x` and the old `instC (myid x)` agree only after unfolding the semireducible `myid`.
-/

class C (n : Nat) where v : Nat
instance instC (n : Nat) : C n := ⟨0⟩
def myid (n : Nat) : Nat := n
def f (a : Nat) [inst : C a] : Nat := inst.v

/-! By default, `dsimp` refuses the rewrite. -/

/--
warning: A rewrite with myid changed an argument of
  f (myid x)
The instance argument
  instC (myid x)
then does not have the expected type at `.instances` transparency, and no usable replacement instance was found. The rewrite was not applied here.

Note: Disable this warning with `set_option dsimp.resynthInstances.warning false`, or the whole check with `set_option dsimp.resynthInstances false`.
---
error: `dsimp` made no progress
-/
#guard_msgs in
example (x : Nat) : @f (myid x) (instC (myid x)) = 0 := by
  dsimp only [myid]

/-! Under `respectTransparency false`, `dsimp` adopts `instC x`. -/

set_option backward.isDefEq.respectTransparency false in
example (x : Nat) : @f (myid x) (instC (myid x)) = 0 := by
  dsimp only [myid]
  guard_target =ₛ @f x (instC x) = 0
  rfl
