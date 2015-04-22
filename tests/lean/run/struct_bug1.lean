variable (A : Type)

structure foo (a : A) :=
(eqpr : a = a)

section
 parameter (B : Type)

 structure foo2 (b : B) :=
 (eqpr : b = b)

 check foo2

 definition tst : B → Type₁ := foo2
end
