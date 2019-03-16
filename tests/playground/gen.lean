def main (xs : list string) : io uint32 :=
let n := xs.head.to_nat in
io.println "prelude\ninductive bool : Type\n| ff : bool\n| tt : bool\n\n" *>
nat.mrepeat n (λ i, io.println ("theorem x" ++ to_string i ++ " : bool := bool.tt")) *>
pure 0
