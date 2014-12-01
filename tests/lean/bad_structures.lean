prelude namespace foo structure prod.{l} (A : Type.{l}) (B : Type.{l}) :=
(pr1 : A) (pr2 : B)

structure prod.{l} (A : Type.{l}) (B : Type.{l}) : Type :=
(pr1 : A) (pr2 : B)

structure prod.{l} (A : Type.{l}) (B : Type.{l}) : Type.{l} :=
(pr1 : A) (pr2 : B)

structure prod.{l} (A : Type.{l}) (B : Type.{l}) : Type.{max 1 l} :=
(pr1 : A) (pr2 : B)
end foo
