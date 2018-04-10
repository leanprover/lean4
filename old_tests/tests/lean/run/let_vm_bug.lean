def f : nat → nat :=
let A := nat in
λ (a : A), a

example : f 0 = 0 :=
rfl
