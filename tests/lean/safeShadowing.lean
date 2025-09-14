def f (x x : Nat) :=
  match x with
  | 0          => x + 1
  | Nat.succ _ => x + 2

def f' :=
  fun (x : Nat) => id fun (x : Nat) =>
    match x with
    | 0          => x + 1
    | Nat.succ _ => x + 2

variable {α : Type}

#check fun (a : α) => a

#check fun {α} (a : α) => a

/-!
This would be safe shadowing, but since it's in the same `fun` it is confusing to have repeated variable names.
-/
#check fun (x x : Nat) => x

/-!
Splitting up the `fun`, safe shadowing applies again.
-/
#check fun (x : Nat) => id fun (x : Nat) => x

/-!
Same lambda, no safe shadowing.
-/
#print f

/-!
Split up lambda, uses safe shadowing.
-/
#print f'

set_option pp.safeShadowing false

#check fun {α} (a : α) => a

#check fun (x x : Nat) => x

#print f

#print f'
