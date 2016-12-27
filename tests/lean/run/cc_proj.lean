open tactic

example (a b c d : nat) (f : nat → nat × nat) : (f d).1 ≠ a → f d = (b, c) → b = a → false :=
by cc

def ex (a b c d : nat) (f : nat → nat × nat) : (f d).2 ≠ a → f d = (b, c) → c = a → false :=
by cc

example (a b c : nat) (f : nat → nat) : (f b, c).1 ≠ f a → f b = f c → a = c → false :=
by cc
