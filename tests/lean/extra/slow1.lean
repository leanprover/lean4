open nat

definition f (a : nat) : nat := a
definition g (a : nat) : nat := zero

example (a b : nat) :
@eq nat
(g (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f a))))))))))))))))))))))
(g (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f b))))))))))))))))))))))
:=
@eq.refl nat (g (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f a))))))))))))))))))))))
