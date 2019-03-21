def main (xs : List String) : IO UInt32 :=
let n := xs.head.toNat in
IO.println "prelude\ninductive Bool : Type\n| ff : Bool\n| tt : Bool\n\n" *>
Nat.mrepeat n (λ i, IO.println ("theorem x" ++ toString i ++ " : Bool := Bool.tt")) *>
pure 0
