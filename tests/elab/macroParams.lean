macro x:ident noWs "(" ys:term,* ")" : term => `($x $ys*)

/-- info: id 1 : Nat -/
#guard_msgs in
#check id(1)

macro "foo" &"only" : tactic => `(tactic| trivial)

example : True := by foo only
