import data.nat data.list
open nat

constant foo (a : nat) : a > 0 → nat

definition bla (a : nat) :=
foo
  (succ (succ a))
  abstract lt.step abstract zero_lt_succ a end  end

print bla
print bla_1
print bla_2

definition test (a : nat) :=
foo
  (succ (succ a))
  abstract [reducible] lt.step abstract [irreducible] zero_lt_succ a end  end

print test_1
print test_2

constant voo {A : Type} (a b : A) : a ≠ b → bool

set_option pp.universes true

open list
definition tst {A : Type} (a : A) (l : list A) :=
voo (a::l) [] abstract by contradiction end

print tst_1
print tst
