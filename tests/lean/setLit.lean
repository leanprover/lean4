structure Foo where
  val := 10

instance : Singleton α (List α) where
  singleton a := [a]

instance : Insert α (List α) where
  insert a as := a :: as

def f1 : Foo := {}

def f2 : List Nat := {}

def f3 : List Nat := {1, 2}

def f4 (a : Nat) : List Nat := {a}

def f5 (val : Nat) : Foo := {val}

def f6 (val : Nat) : List Nat := {val}

def f7 : String := {}

def f8 (val : Nat) : String := { val }
