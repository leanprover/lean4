import Lean



-- https://github.com/leanprover/lean4/issues/4455
def Foo.aaaaaaaa := 1

#eval ([1,2,3].map λ c => Foo.aaaaaaa).length
                                   --^ completion



-- https://github.com/leanprover/lean4/issues/4705
structure Bar where
  foobar : Nat

structure Foo where
  x : Bar

example (f : Foo) : Nat × Nat :=
  ⟨f.x.foobar, f.x.f⟩
                  --^ completion

example (b : Bar) : Nat × Nat :=
  ⟨b.foobar, b.f⟩
              --^ completion



-- https://github.com/leanprover/lean4/issues/5219
structure ContinuousSMul (M X : Type) : Prop where
structure ContinuousAdd (X : Type) : Prop where

theorem Prod.continuousSMul {M X Y : Type} : ContinuousSMul M (X × Y) := ⟨⟩

theorem Prod.continuousAdd {X Y : Type} : ContinuousAdd (X × Y) := ⟨⟩

example : (ContinuousSMul Nat (Nat × Nat)) ∧ (ContinuousAdd (Nat × Nat)) := by
  exact ⟨Prod.continuousSMul, Prod.continuous⟩
                                           --^ completion

example : True ∧ True := by
  exact ⟨trivial, True.in⟩
                       --^ completion
