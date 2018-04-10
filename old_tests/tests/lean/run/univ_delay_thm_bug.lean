lemma foo : ∀B A : Type _, ∀a:A, a=a :=
let x : ∀A, ∀a:A, a=a := @rfl in λB, x
