set_option blast.strategy "cc"
set_option blast.cc.heq true

definition ex1 (a b c a' b' c' : nat) : a = a' → b = b' → c = c' → a + b + c + a = a' + b' + c' + a' :=
by blast

set_option pp.beta true
print ex1
