def Set (α : Type u) : Type u := α → id Prop

mutual
  inductive Even : id (Set Nat)
  | zero : Even 0
  | succ : Odd n → Even n

  inductive Odd : Set Nat
  | succ : Even n → Odd n
end

/--
info: inductive Even : id (Set Nat)
number of parameters: 0
constructors:
Even.zero : Even 0
Even.succ : ∀ {n : Nat}, Odd n → Even n
-/
#guard_msgs in
#print Even

/--
info: inductive Odd : Set Nat
number of parameters: 0
constructors:
Odd.succ : ∀ {n : Nat}, Even n → Odd n
-/
#guard_msgs in
#print Odd
