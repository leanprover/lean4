/-!
# Testing `pp.maxSteps`
-/

/-!
Without setting `pp.maxSteps`, the goal would crash the LSP when trying to create very large JSON.
-/

opaque myAuxiliaryFunction : Nat → Nat → Nat
opaque anotherHelper : Nat → Nat

def f (m : Nat) : Nat → Nat
  | 0   => anotherHelper m
  | n+1 => myAuxiliaryFunction (f (anotherHelper m) n) (f (myAuxiliaryFunction m (anotherHelper m)) n)

set_option pp.maxSteps 10

/--
error: unsolved goals
a b : Nat
⊢ myAuxiliaryFunction
      (myAuxiliaryFunction
        (myAuxiliaryFunction
          (myAuxiliaryFunction
            (myAuxiliaryFunction
              (myAuxiliaryFunction (myAuxiliaryFunction (myAuxiliaryFunction (myAuxiliaryFunction ⋯ ⋯) ⋯) ⋯) ⋯) ⋯)
            ⋯)
          ⋯)
        ⋯)
      ⋯ =
    ⋯
-/
#guard_msgs in
example : f a 10 = b := by
  simp [f]
