import data.nat
open nat

namespace test

constant foo (a : nat) : a > 0 → nat

definition bla (a : nat) :=
foo
  (succ (succ a))
  abstract as foo.prf [irreducible] lt.step (zero_lt_succ a) end

print foo.prf
print bla

end test

print test.bla
print test.foo.prf
