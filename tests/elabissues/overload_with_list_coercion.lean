structure Var : Type := (name : String)
instance Var.nameCoe : HasCoe String Var := ⟨Var.mk⟩

structure A : Type := (u : Unit)
structure B : Type := (u : Unit)

def a : A := A.mk ()
def b : B := B.mk ()

def Foo.chalk : A → List Var → Unit := λ _ _ => ()
def Bar.chalk : B → Unit := λ _ => ()

open Foo
open Bar

/- The following succeeds: -/
#check Foo.chalk a ["foo"] -- succeeds

/-
The following application fails, due to a curious interaction
between coercions and ad-hoc overloading.
-/
#check chalk a ["foo"] -- fails

/-
Note that the first argument clearly distinguishes the two
`chalk` applications, and there are no coercions in play for the first argument.

I am not arguing that we should support this case, merely logging that it surprised me,
and that I can not employ an otherwise desirable use of overloading because of it.

Note: it works if `Foo.chalk` takes `A` and `Var` and we pass `a` and `"foo"`.
-/
