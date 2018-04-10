constant f : nat → nat → nat
constant g : nat → nat

#check f (1 + g 1) $ g 2 + 2
#check f (g 1) $ f (1 + 1) $ g 2
