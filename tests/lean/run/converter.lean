open tactic conv

run_command mk_simp_attr `foo
run_command mk_simp_attr `bla

constant f : nat → nat → nat
@[foo] def f_lemma : ∀ x, f x x = 0 :=
sorry

constant g : nat → nat
@[bla] def g_lemma : ∀ x, g x = x :=
sorry

meta def ex : conv unit :=
   whnf
>> trace_lhs
>> apply_simp_set `bla
>> trace_lhs
>> dsimp
>> trace "after defeq simplifier"
>> trace_lhs
>> change `(f a a)
>> trace_lhs
>> apply_simp_set `foo
>> trace_lhs

example (a b c : nat) : (λ x, g (f (a + 0) (sizeof x))) a = 0 :=
by do
  t ← target,
  (lhs, rhs) ← match_eq t,
  ⟨u, e, some pr⟩ ← ex `eq lhs | failed,
  exact pr
