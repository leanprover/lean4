definition f (n : nat) : nat :=
if n = 100000 then 1 else 0

example (n : nat) : f 100000 = (if (100000 : nat) = 100000 then 1 else 0) :=
by unfold f
-- it is timing out if we use just `rfl`.
