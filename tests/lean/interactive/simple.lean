import logic

namespace tst
definition foo {A B : Type} (a : A) (b : B) := a
definition boo {A : Type} (a : A) := foo a a
end tst

definition pr1 {A : Type} (a b : A) := a