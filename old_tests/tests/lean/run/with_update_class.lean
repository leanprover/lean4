universe variables u

class foo (A : Type u) :=
(x : A)

class bla (A : Type u) extends foo A :=
(y : nat)

def ex {A : Type u} [s : foo A] : bla A :=
{ s with y := 0 }
