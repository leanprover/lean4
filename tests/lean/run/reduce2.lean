def fact : Nat → Nat
| 0     => 1
| (n+1) => (n+1)*fact n


def v1 := fact 10
theorem v1Eq : v1 = fact 10 :=
Eq.refl (fact 10)

new_frontend
set_option trace.Elab.definition true

abbrev v2 := fact 10
theorem v2Eq : v2 = fact 10 :=
Eq.refl (fact 10)
