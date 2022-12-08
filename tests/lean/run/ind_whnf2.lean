def Set (α : Type u) : Type u := α → id Prop

mutual
  inductive Even : id (Set Nat)
  | zero : Even 0
  | succ : Odd n → Even n

  inductive Odd : Set Nat
  | succ : Even n → Odd n
end

#print Even
#print Odd
