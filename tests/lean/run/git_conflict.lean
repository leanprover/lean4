/--
error: unsolved goals
case right
⊢ 0 = 0
-/
#guard_msgs in
example : True ∧ 0 = 0 := by
<<<<<<<
  refine ⟨.intro, ?right⟩
  done
=======
    refine ⟨?left, rfl⟩
  done
>>>>>>>

/--
error: unsolved goals
case left
⊢ True
-/
#guard_msgs in
example : True ∧ 0 = 0 := by
<<<<<<<
  refine ⟨.intro, ?right⟩
  done
=======
    refine ⟨?left, rfl⟩
  done
>>>>>>>
