prelude namespace foo structure {l} prod (A : Sort l) (B : Sort l) :=
(pr1 : A) (pr2 : B)

structure {l} prod1 (A : Sort l) (B : Sort l) : Type :=
(pr1 : A) (pr2 : B)

structure {l} prod2 (A : Sort l) (B : Sort l) : Sort l :=
(pr1 : A) (pr2 : B)

structure {l} prod3 (A : Sort l) (B : Sort l) : Sort (max 1 l) :=
(pr1 : A) (pr2 : B)
end foo
