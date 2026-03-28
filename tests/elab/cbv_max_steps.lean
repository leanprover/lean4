-- Default limit works on a normal computation
example : (List.replicate 10 1).length = 10 := by cbv

-- Low limit triggers "maximum number of steps exceeded"
set_option cbv.maxSteps 10 in
/--
error: `simp` failed: maximum number of steps exceeded
-/
#guard_msgs (error) in
example : (List.replicate 10 1).length = 10 := by cbv
