inductive LE' (n : Nat) : Nat → Prop where
  | refl {} : LE' n n

#check @LE'.refl
#print LE'
