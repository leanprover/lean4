import logic

namespace tst
definition foo {A B : Type} (a : A) (b : B) := a
definition boo {A : Type} (a : A) := foo a a
end tst

theorem tst {A : Type} (a b : A) : tst.foo a b = a :=
rfl
