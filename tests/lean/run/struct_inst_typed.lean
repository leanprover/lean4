
#check { fst := 10, snd := 20 : Nat × Nat }

structure S :=
(x : Nat) (y : Bool) (z : String)


#check { x := 10, y := true, z := "hello" : S }

#check { fst := "hello", snd := "world" : Prod _ _ }
