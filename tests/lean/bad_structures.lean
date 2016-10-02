prelude namespace foo structure {l} prod (A : Type l) (B : Type l) :=
(pr1 : A) (pr2 : B)

structure {l} prod1 (A : Type l) (B : Type l) : Type :=
(pr1 : A) (pr2 : B)

structure {l} prod2 (A : Type l) (B : Type l) : Type l :=
(pr1 : A) (pr2 : B)

structure {l} prod3 (A : Type l) (B : Type l) : Type (max 1 l) :=
(pr1 : A) (pr2 : B)
end foo
