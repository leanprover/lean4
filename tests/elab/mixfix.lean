

infix:65 " +' " => Add.add
infix:70 " *' " => Mul.mul
infixr:30 " OR " => Or
prefix:40 "NOT " => Not

theorem ex (a b c d : Nat) (p : Prop) : (NOT p OR a = b*'c +' c*'a OR a = b *' c) = (¬ p ∨ a = b*c + c*a ∨ a = b * c) :=
rfl
