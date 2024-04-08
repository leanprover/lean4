example (b1 b2 : Bool) :
  (match b1 with | true => 0 | false => (if b2 then 0 else if b2 then 42 else 0)) = 0 := by
  split
  · rfl
  · -- NB: the nested `if b2` is untouched
    show (if b2 = true then 0 else if b2 = true then 42 else 0) = 0
    split <;> rfl

example (b1 b2 : Bool) :
  (if b1 then 0 else (if b2 then 0 else if b2 then 42 else 0)) = 0 := by
  split
  · rfl
  · -- NB: the nested `if b2` is untouched
    show (if b2 = true then 0 else if b2 = true then 42 else 0) = 0
    split <;> rfl

example (b1 b2 : Bool) (h : b2 = true) :
  (if b1 then 0 else (if b2 then 0 else if b2 then 42 else 0)) = 0 := by
  split
  · rfl
  · -- NB: The unrealted `if b2` has been simplified, maybe it shouldn't
    show 0 = 0
    rfl
