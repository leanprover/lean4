/-!
The `Float.ofScientific` instance was sometimes off by 1ulp.
-/

/-- info: 4546025755234222441 -/
#guard_msgs in
#eval (0.0000867 : Float).toBits
