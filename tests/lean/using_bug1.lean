variables a b c d : Nat
axiom H : a + (b + c) = a + (b + d)
using Nat
check add_succr a

theorem mul_zerol2 (a : Nat) : 0 * a = 0
:= induction_on a
    (have 0 * 0 = 0 : trivial)
    (λ (n : Nat) (iH : 0 * n = 0),
        calc  0 * (n + 1)  =  (0 * n) + 0 : mul_succr 0 n
                      ...  =  0 + 0       : { iH }
                      ...  =  0           : trivial)
