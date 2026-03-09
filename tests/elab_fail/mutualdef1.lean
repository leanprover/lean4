--

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

mutual

def f (x : Nat) : Nat → Nat
| 0   => 1
| x+1 => g x

unsafe def g (x : Nat) : Nat → Nat -- cannot mix safe and unsafe definitions
| 0   => 2
| x+1 => f x

end
