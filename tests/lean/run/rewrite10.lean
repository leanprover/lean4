import data.nat
open nat

section
  variables (a b c d e : nat)

  theorem T (H1 : a = b) (H2 : b = c + 1) (H3 : c = d) (H4 : e = 1 + d) : a = e :=
  by rewrite [H1, H2, H3, add.comm, -H4]
end

example (x y : ℕ) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
by rewrite [*mul.left_distrib, *mul.right_distrib, -add.assoc]

definition even (a : nat) := ∃b, a = 2*b

theorem even_plus_even {a b : nat} (H1 : even a) (H2 : even b) : even (a + b) :=
exists.elim H1 (fun (w1 : nat) (Hw1 : a = 2*w1),
exists.elim H2 (fun (w2 : nat) (Hw2 : b = 2*w2),
  exists.intro (w1 + w2)
    begin
      rewrite [Hw1, Hw2, mul.left_distrib]
    end))

theorem T2 (a b c : nat) (H1 : a = b) (H2 : b = c + 1) : a ≠ 0 :=
calc
  a     = succ c : by rewrite [H1, H2, add_one]
    ... ≠ 0      : succ_ne_zero c
