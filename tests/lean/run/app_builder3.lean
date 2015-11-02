constant f : ∀ (A : Type) (a b c : A), a = c → A

variables a b c : nat
variables H : a = b

#app_builder f [false, false, true, false, true] c, H
#app_builder f [false, true, true, false, true] a, c, H
