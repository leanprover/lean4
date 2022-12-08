inductive LE' : Nat → Nat → Prop where
  | refl (n : Nat) : LE' n n

#check @LE'.refl
#print LE'
