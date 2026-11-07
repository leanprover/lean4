/-!
`Sym.canon` must canonicalize instances that are structure fields rather than global instances,
e.g. `NatCast R` via `Grind.Semiring.natCast`. The same field can be spelled through different
parent paths (`Ring.toSemiring (CommRing.toRing _)` vs `CommSemiring.toSemiring
(CommRing.toCommSemiring _)`), and `grind`'s ring module compares instances by pointer, so the
paths must converge. Before the fix the `Sym.simp` normalizer produced both spellings in one
term and `grind` reported `ring term with unexpected instance`.
-/
open Lean Grind

section legacy
variable (R : Type) [CommRing R] (a : R)

-- With the legacy normalizer every cast comes from `smul_nat_eq_mul`, so the identity holds even
-- with `↑m`, `↑n` as atoms, but the ring module must not report them as unexpected instances.
#guard_msgs in
set_option trace.sym.issues true in
example (m n : Nat) : (m + n) • a = m • a + n • a := by grind

end legacy

set_option backward.grind.normalizer false

section CommRing
variable (R : Type) [CommRing R] (a b : R)

example (m n : Nat) : (m + n) • a = m • a + n • a := by grind
example (m n : Nat) : (m * n) • a = m • (n • a) := by grind
example (m n : Nat) : (m * n) • (a * b) = (m • a) * (n • b) := by grind
example (m n : Int) : (m + n) • a = m • a + n • a := by grind
example (m n : Int) : (m * n) • (a * b) = (m • a) * (n • b) := by grind

end CommRing

section CommSemiring
variable (R : Type) [CommSemiring R] (a b : R)

example (m n : Nat) : (m + n) • a = m • a + n • a := by grind
example (m n : Nat) : (m * n) • (a * b) = (m • a) * (n • b) := by grind

end CommSemiring
