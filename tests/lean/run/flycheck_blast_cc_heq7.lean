set_option blast.cc.heq true

set_option trace.app_builder true
definition t3 (a b : nat) : (a = b) == (b = a) :=
by blast
