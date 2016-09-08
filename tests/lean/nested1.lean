--
open nat

namespace test

constant foo (a : nat) : a > 0 → nat

noncomputable definition bla (a : nat) :=
foo
  (succ (succ a))
  abstract as foo.prf lt.step (zero_lt_succ a) end

attribute [irreducible] foo.prf

print foo.prf
print bla

end test

print test.bla
print test.foo.prf
