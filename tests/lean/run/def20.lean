def f : Char → Nat
| 'a' => 0
| 'b' => 1
| 'c' => 2
| 'd' => 3
| 'e' => 4
| _   => 5

theorem ex1 : (f 'a', f 'b', f 'c', f 'd', f 'e', f 'f') = (0, 1, 2, 3, 4, 5) :=
rfl

def g : Nat → Nat
| 100000 => 0
| 200000 => 1
| 300000 => 2
| 400000 => 3
| _      => 5

theorem ex2 : (g 100000, g 200000, g 300000, g 400000, g 0) = (0, 1, 2, 3, 5) :=
rfl

def h : String → Nat
| "hello" => 0
| "world" => 1
| "bla"   => 2
| "boo"   => 3
| _       => 5

theorem ex3 : (h "hello", h "world", h "bla", h "boo", h "zoo") = (0, 1, 2, 3, 5) :=
rfl

def r : String × String → Nat
| ("hello", "world") => 0
| ("world", "hello") => 1
| _                  => 2

theorem ex4 : (r ("hello", "world"), r ("world", "hello"), r ("a", "b")) = (0, 1, 2) :=
rfl

example (a b : String) (h : a.length > 10) : r (a, b) = 2 := by
  simp [r]
  split
  next h => injection h with h; subst h; contradiction
  next h => injection h with h; subst h; contradiction
  next => decide
