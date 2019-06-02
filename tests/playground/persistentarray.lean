import init.data.persistentarray

abbrev MyArray := PersistentArray Nat
-- abbrev MyArray := Array Nat

def mkMyArray (n : Nat) : MyArray :=
n.fold (λ i s, s.push i) { PersistentArray . }
-- n.fold (λ i s, s.push i) Array.empty

def check (n : Nat) (p : Nat → Nat → Bool) (s : MyArray) : IO Unit :=
n.mfor $ λ i, unless (p i (s.get i)) (throw (IO.userError ("failed at " ++ toString i ++ " " ++ toString (s.get i))))

def inc1 (n : Nat) (s : MyArray) : MyArray :=
n.fold (λ i s, s.set i (s.get i + 1)) s

def checkId (n : Nat) (s : MyArray) : IO Unit :=
check n (==) s

def main (xs : List String) : IO Unit :=
do
let n := xs.head.toNat,
let t := mkMyArray n,
checkId n t,
let t := inc1 n t,
check n (λ i v, v == i + 1) t,
IO.println t.size,
IO.println t.stats,
pure ()
