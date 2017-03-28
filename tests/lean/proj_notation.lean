structure myprod (A B : Type) :=
(fst : A) (snd : B)

variable p : myprod nat nat
variable f : nat → nat

#check p^.fst
#check p^.1
#check p^.2
#check p^.snd

#check f p^.1
#check p^.1 + p^.2

example (A B : Type) : A × B → B × A  :=
λ h, ⟨h^.2, h^.1⟩

example (A B : Type) : A × B → B × A  :=
λ h, ⟨h^.snd, h^.fst⟩

structure position (A B : Type) :=
(x : A) (y : B)

structure car :=
(pos : position nat nat) (cheap : bool)

#check λ c : car, c^.pos^.x

#check λ c : car, c^.fst

#check λ c : car, c^.0

#check λ c : car, c^.3

#check λ n : nat, n^.1

#check p.1
#check p.2
#check λ c : car, c.1.2
