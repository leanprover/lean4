-- Regression test for https://github.com/leanprover/lean4/issues/13371
-- The LCNF cache must distinguish entries cached in irrelevant positions
-- (where noncomputable uses are tolerated) from those in relevant positions.
structure Hom [Inhabited Unit] where
  toFun : Unit

noncomputable instance inst : Inhabited Unit := ⟨Classical.choice ⟨()⟩⟩

/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'inst', which is 'noncomputable'
-/
#guard_msgs in
def test : Hom := ⟨default⟩
