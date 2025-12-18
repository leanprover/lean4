instance : Singleton α (List α) where
  singleton a := [a]

instance : Insert α (List α) where
  insert a as := a :: as

def f (a : List Nat) := a

/--
info: f {1, 2, 3} : List Nat
-/
#guard_msgs in
#check f {1, 2, 3}

/--
info: f {1} : List Nat
-/
#guard_msgs in
#check f {1}

/--
info: f ∅ : List Nat
-/
#guard_msgs in
#check f {}
