variable q : Nat → Bool
variable f : Nat → Nat → Nat

theorem T1 (a b : Nat) (H1 : a = b) (H2 : q (f (f a a) (f a a)))  :  q (f (f a b) (f a a))
:= subst H2 H1

check @subst
set_option pp::implicit true
print environment 1
