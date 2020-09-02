new_frontend


mutual

def f (x : Nat) : Nat → Nat
| 0   => 1
| x+1 => g x

def g (x : Bool) : Nat → Nat -- type mismatch at parameter
| 0   => 2
| x+1 => f x

end

mutual

def f (x : Nat) : Nat → Nat
| 0   => 1
| x+1 => g x

def g (b : Bool) : Nat → Nat -- name mismatch at parameter
| 0   => 2
| x+1 => f x

end


mutual

def f (x : Nat) : Nat → Nat
| 0   => 1
| x+1 => g x

def g {x : Nat} : Nat → Nat -- binder annotation mistmatch
| 0   => 2
| x+1 => f x

end

mutual

def f (x : Nat) (y : Nat) : Nat → Nat
| 0   => 1
| x+1 => g x

def g (x : Nat) : Nat → Nat -- number of parameters mistmatch
| 0   => 2
| x+1 => f x

end

mutual

def f.{u} (x : Nat) : Nat → Nat
| 0   => 1
| x+1 => g x

def g (x : Nat) : Nat → Nat -- universe parameter mistmatch
| 0   => 2
| x+1 => f x

end


mutual

def f (x : Nat) : Nat → Nat
| 0   => 1
| x+1 => g x

theorem g (x : Nat) : Nat → Nat -- cannot mix theorems and definitions
| 0   => 2
| x+1 => f x

end

mutual

def f  : Nat → Nat
| 0   => 1
| x+1 => g x

example : Nat := -- cannot mix examples and definitions
g 10

end
