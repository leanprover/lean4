abbrev Map1 : Type := RBMap Nat Bool (λ a b, a < b)
abbrev Map2 : Type := HashMap Nat Bool

def mkMap1Aux : Nat → Map1 → Map1
| 0 m := m
| (n+1) m := mkMap1Aux n (m.insert n (n % 10 = 0))

def mkMap2Aux : Nat → Map2 → Map2
| 0 m := m
| (n+1) m := mkMap2Aux n (m.insert n (n % 10 = 0))

def mkMap1 (n : Nat) :=
mkMap1Aux n {}

def mkMap2 (n : Nat) :=
mkMap2Aux n {}

def tst1 (n : Nat) : IO Unit :=
do let m := mkMap1 n,
   let v := m.fold (λ (r : Nat) (k : Nat) (v : Bool), if v then r + 1 else r) 0,
   IO.println ("Result " ++ toString v)

def tst2 (n : Nat) : IO Unit :=
do let m := mkMap2 n,
   let v := m.fold (λ (r : Nat) (k : Nat) (v : Bool), if v then r + 1 else r) 0,
   IO.println ("Result " ++ toString v)

def main (xs : List String) : IO Unit :=
timeit "tst1" (tst1 xs.head.toNat) *>
timeit "tst2" (tst2 xs.head.toNat)
