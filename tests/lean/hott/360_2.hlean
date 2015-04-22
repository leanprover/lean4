open is_trunc
--structure is_contr [class] (A : Type) : Type

section
parameters {P : Π(A : Type), A → Type}

definition my_contr {A : Type} [H : is_contr A] (a : A) : P A a := sorry

definition foo2
(A : Type)
(B : A → Type)
(a : A)
(x : B a)
(H : Π (a : A), is_contr (B a))  --(H : is_contr (B a))
  : P (B a) x :=
by apply my_contr
end
