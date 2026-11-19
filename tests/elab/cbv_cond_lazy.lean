def slow : Nat → Bool
  | 0 => false
  | n+1 => slow n

-- `cbv` evaluates only the branch of `cond` that the condition selects.
-- Evaluating `slow 1000` exceeds the step limit.
set_option cbv.maxSteps 100

example : (bif true then true else slow 1000) = true := by cbv

example : (bif false then slow 1000 else true) = true := by cbv

example : (bif 2 == 2 then 1 else if slow 1000 then 2 else 3) = 1 := by cbv

example : (bif slow 3 then slow 1000 else true) = true := by cbv

example : (bif true then (· + 1) else if slow 1000 then id else (· + 2)) 4 = 5 := by cbv
