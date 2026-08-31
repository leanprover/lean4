/--
@ +4:4...8
error: Redundant alternative: Any expression matching
  0, x✝
will match one of the preceding alternatives
-/
#guard_msgs (positions := true) in
example : Nat → Nat → Nat
  | _ + 1, _ => 2  -- error was here (bad)
  | 0, _
  | 0, _ => 1 -- now error is here (good)

/--
@ +4:4...8
error: Redundant alternative: Any expression matching
  0, x✝
will match one of the preceding alternatives
-/
#guard_msgs (positions := true) in
example : Nat → Nat → Nat
  | _ + 1, _ => 2
  | 0, _ => 1
  | 0, _ => 1 -- error here (good)

/--
@ +3:4...12
error: Redundant alternative: Any expression matching
  n✝.succ.succ, x✝
will match one of the preceding alternatives
-/
#guard_msgs (positions := true) in
example : Nat → Nat → Nat
  | _ + 2, _ => 2
  | _ + 2, _ => 2 -- error here (good)
  | 0, _
  | 1, _ => 1
