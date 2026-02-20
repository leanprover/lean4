structure Foo where
  (p : Nat → Prop)
  (q : String → Prop)
  [inst0 : DecidablePred p]
  [inst1 : DecidablePred q]

example : Foo := {
  p := fun n => n < 9
  q := fun s => s.length < 9
}

structure Bar where
  (p : Prop)
  (q : Prop)
  [inst0 : Decidable p]
  [inst1 : Decidable q]

example : Bar := {
  p := True
  q := False
}

structure Boo where
  x : Nat
  y : Nat  := x + 1
  p : Prop := x < y
  [i : Decidable p]

example : Boo := {
  x := 0
}
