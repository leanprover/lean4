def f (x x : Nat) :=
  match x with
  | 0          => x + 1
  | Nat.succ _ => x + 2

variable {α : Type}

#check fun (a : α) => a

#check fun {α} (a : α) => a

#check fun (x x : Nat) => x

#print f

set_option pp.safeShadowing false

#check fun {α} (a : α) => a

#check fun (x x : Nat) => x

#print f
