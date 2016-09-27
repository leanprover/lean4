universe variables u v

structure Func :=
(A : Type u) (B : Type v) (fn : A → B → A)

instance F_to_fn : has_coe_to_fun Func :=
{ F   := λ f, f^.A → f^.B → f^.A,
  coe := λ f, f^.fn }

variables (f : Func) (a : f^.A) (b : f^.B)
check (f a b)
