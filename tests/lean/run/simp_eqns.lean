def f : nat → nat
| 0     := 1
| (n+1) := f n + 10

example (n : nat) : f (n+1) = f n + 10 :=
by simp [f]

example (n : nat) : f 0 = 1 :=
by simp [f]

def g : nat → nat
| 0     := 2
| (n+1) :=
  match f n with
  | 0 := 0
  | 1 := 3
  | _ := 4
  end

example (n : nat) : g (0+1) = 3 :=
by simp [g, f]
