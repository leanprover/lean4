/- Recursive functions -/

#print Nat -- Nat is an inductive datatype

def fib (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | 1 => 1
  | n+2 => fib (n+1) + fib n

example : fib 5 = 8 := rfl

example : fib (n+2) = fib (n+1) + fib n := rfl

#print fib
/-
def fib : Nat → Nat :=
fun n =>
  Nat.brecOn n fun n f =>
    (match (motive := (n : Nat) → Nat.below n → Nat) n with
      | 0 => fun x => 1
      | 1 => fun x => 1
      | Nat.succ (Nat.succ n) => fun x => x.fst.fst + x.fst.snd.fst.fst)
      f
-/
