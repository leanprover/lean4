@[reducible] def map : Type := Rbmap Nat Bool (<)

def mkMapAux : Nat → map → map
| 0 m := m
| (n+1) m := mkMapAux n (m.insert n (n % 10 = 0))

def mkMap (n : Nat) :=
mkMapAux n (mkRbmap Nat Bool (<))

def main (xs : List String) : IO UInt32 :=
let m := mkMap xs.head.toNat in
let v := Rbmap.fold (λ (k : Nat) (v : Bool) (r : Nat), if v then r + 1 else r) m 0 in
IO.println (toString v) *>
pure 0
