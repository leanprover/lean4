open nat

definition f (n : nat) (H : n = n) := λm, id (n + m)
#print f

set_option pp.binder_types true
#print f
