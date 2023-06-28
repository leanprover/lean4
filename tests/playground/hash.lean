import init.data.hashmap.basic

def mkMap (s : String) : Nat → HashMap String Nat → HashMap String Nat
| 0     m := m
| (n+1) m := mkMap n (m.insert (s ++ toString n) n)

def checkMap (s : String) (m : HashMap String Nat) : Nat → IO Unit
| 0     := pure ()
| (n+1) := do
  let key := s ++ toString n,
  unless (m.contains key) (throw $ IO.userError "not found"),
  IO.println (key ++ " |-> " ++ toString (m.find key)),
  checkMap n

def main (xs : List String): IO Unit :=
do let s := "base",
   let n := xs.head.toNat,
   let m := mkMap s n {},
   checkMap s m n
