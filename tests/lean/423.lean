universe u

#check fun {T : Sort u} (a : T) => a + 0

#check fun {T : Sort u} (a : T) [Add T] [OfNat T 0] => a + 0
