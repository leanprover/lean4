def f : Fin 2 → Nat
  | 0 => 5
  | 1 => 45

example : f 0 = 5 := rfl
example : f 1 = 45 := rfl

def g : Fin 11 → Nat
  | 0 => 5
  | 1 => 10
  | 2 => 15
  | 3 => 2
  | 4 => 48
  | 5 => 0
  | 6 => 87
  | 7 => 64
  | 8 => 32
  | 9 => 64
  | 10 => 21

def h : Fin 15 → Nat
  | 0 => 5
  | 1 => 45
  | _ => 50
