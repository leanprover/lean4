namespace test

instance : has_add nat :=
{add := nat.succ}

instance : semigroup nat :=
{mul       := nat.add,
 mul_assoc := trivial }

end test
