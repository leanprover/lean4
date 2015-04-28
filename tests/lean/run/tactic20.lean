import logic
open tactic

infixl `;`:15 := tactic.and_then

definition assump := eassumption

theorem tst {A : Type} {a b c : A} (H1 : a = b) (H2 : b = c) : a = c
:= by apply eq.trans; assump; assump
