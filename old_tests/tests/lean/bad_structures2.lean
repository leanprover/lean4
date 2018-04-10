structure foo :=
(x : bool)

structure boo :=
(x : nat)

structure bla extends foo, boo

structure boo2 :=
{x : bool}

structure bla extends foo, boo2

structure bla extends foo :=
(x : nat)

structure bla extends foo :=
( : nat)

structure bla extends foo :=
mk :: y z : nat

structure bla2 extends nat

structure bla2 extends Type


structure bla2 : Prop :=
(x : Prop)

structure bla3 : Prop :=
(x : nat)
