import data.finset data.num data.nat data.int algebra.ring
open finset num nat int algebra

check @finset.insert _ _ 1 (@finset.empty ℕ)

check '{(1:nat), 2, 3}
check ('{1, 2, 3} : finset ℕ)
check ('{1, 2, 3} : finset ℕ)  -- finset ℕ
check ('{1, 2, 3} : finset ℤ)  -- finset ℤ

example : finset nat :=
insert 1 (insert 2 (insert 3 empty))

check insert 1 (insert 2 (insert 3 empty)) -- finset num
check (insert 1 (insert 2 (insert 3 empty)) : finset nat)

check (insert (1:nat) (insert (2:nat) (insert (3:nat) empty)))

definition foo_nat (x : finset ℕ) : finset ℕ := x
definition foo_int (x : finset ℤ) : finset ℤ := x

check foo_nat '{1, 2, 3}  -- finset ℕ
check foo_int '{1, 2, 3}  -- finset ℤ
