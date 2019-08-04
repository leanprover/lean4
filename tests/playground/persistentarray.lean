import init.data.persistentarray

abbrev MyArray := PersistentArray Nat
-- abbrev MyArray := Array Nat

def mkMyArray (n : Nat) : MyArray :=
n.fold (λ i s => s.push i) { PersistentArray . }
-- n.fold (λ i s, s.push i) Array.empty

def check (n : Nat) (p : Nat → Nat → Bool) (s : MyArray) : IO Unit :=
n.mfor $ λ i => unless (p i (s.get i)) (throw (IO.userError ("failed at " ++ toString i ++ " " ++ toString (s.get i))))

def inc1 (n : Nat) (s : MyArray) : MyArray :=
n.fold (λ i s => s.set i (s.get i + 1)) s

def checkId (n : Nat) (s : MyArray) : IO Unit :=
check n (fun a b => a == b) s

def popTest (n : Nat) (p : Nat → Nat → Bool) (s : MyArray) : IO MyArray :=
n.mfold (λ i s => do
  -- IO.println i;
  check (n - i) p s;
  let s := s.pop;
  -- IO.println s.stats;
  -- IO.println ("size: " ++ toString s.size ++ ", tailOff " ++ toString s.tailOff ++ ", shift: " ++ toString s.shift);
  -- IO.println s.tail;
  pure s)
  s

def main (xs : List String) : IO Unit :=
do
let n := xs.head.toNat;
let t := mkMyArray n;
checkId n t;
let t := inc1 n t;
check n (λ i v => v == i + 1) t;
IO.println t.size;
IO.println t.stats;
IO.println "popping...";
t ← popTest (n - 33) (λ i v => v == i + 1) t;
IO.println t.size;
check 33 (λ i v => v == i + 1) t;
let t : MyArray := (1000 : Nat).fold (fun i s => s.push i) t;
check t.size (λ i v => if i < 33 then v == i + 1 else v == i - 33) t;
IO.println t.size;
IO.println t.stats;
t ← popTest t.size (λ i v => if i < 33 then v == i + 1 else v == i - 33) t;
IO.println t.size;
IO.println t.stats;
pure ()
