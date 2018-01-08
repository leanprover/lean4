inductive test : nat -> list nat -> Prop
| zero: test 0 list.nil
--n remains even
| nil: forall {n: nat}, test n list.nil -> test (n+2) list.nil
--n flips between even and odd
| cons: forall {n i: nat} {is: list nat}, test n is -> test (n+3) (list.cons i is)

lemma example3 : forall (n m: nat), test (n+n) [m] -> false :=
begin
intros n m,
generalize def_n' : n + n = n',
generalize def_is : [m] = is,
intro h,
revert def_n' def_is,
cases h; try {intros, contradiction}, -- smart unfolding prevents the generation of unwieldy terms,
trace_state,
have : nat.succ (nat.add h_n (nat.add 2 0)) = h_n + 3, from rfl,
simp [this], intro h_1,
have : n + n = h_n + 3 → false, from sorry,
intros,
exact this h_1,
end
