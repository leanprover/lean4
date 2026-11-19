
/-- info: (10, 20) : Nat × Nat -/
#guard_msgs in #check { fst := 10, snd := 20 : Nat × Nat }

structure S where
  (x : Nat) (y : Bool) (z : String)


/-- info: { x := 10, y := true, z := "hello" } : S -/
#guard_msgs in #check { x := 10, y := true, z := "hello" : S }

/-- info: ("hello", "world") : String × String -/
#guard_msgs in #check { fst := "hello", snd := "world" : Prod _ _ }
