def check (b : Bool) : IO Unit :=
unless b $ IO.println "ERROR"

def sz {α β : Type} {lt : α → α → Bool} (m : RBMap α β lt) : Nat :=
m.fold (fun sz _ _ => sz+1) 0

def depth {α β : Type} {lt : α → α → Bool} (m : RBMap α β lt) : Nat :=
m.depth Nat.max

def tst1 : IO Unit :=
do let Map := RBMap String Nat (fun a b => a < b);
   let m : Map := {};
   let m := m.insert "hello" 0;
   let m := m.insert "world" 1;
   check (m.find "hello" == some 0);
   check (m.find "world" == some 1);
   let m := m.erase "hello";
   check (m.find "hello" == none);
   check (m.find "world" == some 1);
   pure ()

def tst2 : IO Unit :=
do let Map := RBMap Nat Nat (fun a b => a < b);
   let m : Map := {};
   let n : Nat := 10000;
   let m := n.fold (fun i (m : Map) => m.insert i (i*10)) m;
   check (m.all (fun k v => v == k*10));
   check (sz m == n);
   IO.println (">> " ++ toString (depth m) ++ ", " ++ toString (sz m));
   let m := (n/2).fold (fun i (m : Map) => m.erase (2*i)) m;
   check (m.all (fun k v => v == k*10));
   check (sz m == n / 2);
   IO.println (">> " ++ toString (depth m) ++ ", " ++ toString (sz m));
   pure ()

abbrev Map := RBMap Nat Nat (fun a b => a < b)

def mkRandMap (max : Nat) : Nat → Map → Array (Nat × Nat) → IO (Map × Array (Nat × Nat))
| 0,     m, a => pure (m, a)
| n+1,   m, a => do
  k ← IO.rand 0 max;
  v ← IO.rand 0 max;
  if m.find k == none then do
    let m := m.insert k v;
    let a := a.push (k, v);
    mkRandMap n m a
  else
    mkRandMap n m a

def tst3 (seed : Nat) (n : Nat) (max : Nat) : IO Unit :=
do IO.setRandSeed seed;
   (m, a) ← mkRandMap max n {} Array.empty;
   check (sz m == a.size);
   check (a.all (fun ⟨k, v⟩ => m.find k == some v));
   IO.println ("tst3 size: " ++ toString a.size);
   let m := a.iterate m (fun i ⟨k, v⟩ m => if i.val % 2 == 0 then m.erase k else m);
   check (sz m == a.size / 2);
   a.iterateM () (fun i ⟨k, v⟩ _ => when (i.val % 2 == 1) (check (m.find k == some v)));
   IO.println ("tst3 after, depth: " ++ toString (depth m) ++ ", size: " ++ toString (sz m));
   pure ()

def main (xs : List String) : IO Unit :=
tst1 *> tst2 *>
tst3 1 1000 20000 *>
tst3 2 1000 40000 *>
tst3 3 100  4000 *>
tst3 4 5000 100000 *>
tst3 5 1000 40000 *>
pure ()
