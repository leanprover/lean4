variables a b c d : Nat
axiom H : a + (b + c) = a + (b + d)

set_option pp::implicit true

using Nat
check add_succr a

scope

theorem mul_zerol2 (a : Nat) : 0 * a = 0
:= induction_on a
    (have 0 * 0 = 0 : mul_zeror 0)
    (λ (n : Nat) (iH : 0 * n = 0),
        calc  0 * (n + 1)  =  (0 * n) + 0 : mul_succr 0 n
                      ...  =  0 + 0       : { iH }
                      ...  =  0           : add_zeror 0)
end