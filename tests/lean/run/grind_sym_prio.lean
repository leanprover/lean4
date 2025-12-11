module
opaque q : Nat → Prop
opaque p : Nat → Prop

attribute [grind symbol default] HAdd.hAdd

/-- info: foo: [@HAdd.hAdd `[Nat] `[Nat] `[Nat] `[instHAdd] #6 #5] -/
#guard_msgs (info) in
@[grind!? =>] theorem foo (x y : Nat) : x + y < 10 → q x → p x → p y → q y → x = y := by
  sorry

attribute [grind symbol high] p

/-- info: bla: [p #6, p #5] -/
#guard_msgs (info) in
@[grind? =>] theorem bla (x y : Nat) : x + y < 10 → q x → p x → p y → q y → x = y := by
  sorry
