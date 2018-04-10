definition f (n : nat) : nat :=
if n = 100000 then 1 else 0

example (n : nat) : f 100000 = (if (100000 : nat) = 100000 then 1 else 0) :=
rfl

example (n : nat) : f 100000 = (if (100000 : nat) = 100000 then 1 else 0) :=
by unfold f

example (n : nat) : f 100000 = (if (100000 : nat) = 100000 then 1 else 0) :=
by simp [f]

example (n : nat) : f 100000 = (if (100000 : nat) = 100000 then 1 else 0) :=
by dsimp [f]; refl

example (n : nat) : f 100000 = (if (100000 : nat) = 100000 then 1 else 0) :=
by delta f; refl
