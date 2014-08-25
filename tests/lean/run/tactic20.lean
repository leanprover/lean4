import logic
using tactic

definition assump := eassumption

theorem tst {A : Type} {a b c : A} (H1 : a = b) (H2 : b = c) : a = c
:= by apply trans; assump; assump
