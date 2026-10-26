/-!
Benchmarks for the kernel checking of the `grind` ring solver's certificates on Gröbner basis
problems whose proofs have hundreds of `Lean.Grind.CommRing.Stepwise` steps over large
polynomials: Newton's identities for five variables, in characteristic zero and eleven, and the
cyclic-4 system. Kernel checking takes most of the time.
-/

open Lean.Grind

example [CommRing α] [NoNatZeroDivisors α] (a b c d e : α) :
    a + b + c + d + e = 1 → a^2 + b^2 + c^2 + d^2 + e^2 = 5 → a^3 + b^3 + c^3 + d^3 + e^3 = 16 →
    a^4 + b^4 + c^4 + d^4 + e^4 = 25 → a^5 + b^5 + c^5 + d^5 + e^5 = 66 →
    a^6 + b^6 + c^6 + d^6 + e^6 = 158 := by grind

example [CommRing α] [IsCharP α 11] [NoNatZeroDivisors α] (a b c d e : α) :
    a + b + c + d + e = 1 → a^2 + b^2 + c^2 + d^2 + e^2 = 5 → a^3 + b^3 + c^3 + d^3 + e^3 = 16 →
    a^4 + b^4 + c^4 + d^4 + e^4 = 25 → a^5 + b^5 + c^5 + d^5 + e^5 = 66 →
    a^6 + b^6 + c^6 + d^6 + e^6 = 158 := by grind

example (a b c d e : Int) :
    a + b + c + d + e = 1 → a^2 + b^2 + c^2 + d^2 + e^2 = 5 → a^3 + b^3 + c^3 + d^3 + e^3 = 16 →
    a^4 + b^4 + c^4 + d^4 + e^4 = 25 → a^5 + b^5 + c^5 + d^5 + e^5 = 66 →
    a^6 + b^6 + c^6 + d^6 + e^6 = 158 := by grind

example [CommRing α] (x0 x1 x2 x3 : α) :
    x0 + x1 + x2 + x3 = 0 → x0*x1 + x0*x3 + x1*x2 + x2*x3 = 0 →
    x0*x1*x2 + x0*x1*x3 + x0*x2*x3 + x1*x2*x3 = 0 → x0*x1*x2*x3 - 1 = 0 →
    x1*x2 - x1*x3 + x2^2*x3^4 + x2*x3 - 2*x3^2 = 0 := by grind
