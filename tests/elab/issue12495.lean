-- Regression test for https://github.com/leanprover/lean4/issues/12495
-- Equational theorem generation fails for structurally recursive definition
-- using a Box-like wrapper.

structure Box (α : Type u) where
  data : α

structure Rec where
  base? : Option (Box Rec)

def test (self : Rec) : List (Box Rec) :=
  match self with
  | {base? := none, ..} => []
  | {base? := some base, ..} => base :: test base.data
termination_by structural self

-- unfold should work, meaning equational theorems are generated.
example : test { base? := none } = [] := by
  unfold test; rfl

-- Check that the unfold equation exists and can be applied
#check @test.eq_unfold
