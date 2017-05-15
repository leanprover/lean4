open smt_tactic

constant p : nat → nat → Prop
constant f : nat → nat
axiom pf (a : nat) : p (f a) (f a) → p a a

lemma ex1 (a b c : nat) : a = b + 0 → a + c = b + c :=
by using_smt $ do
  pr ← tactic.to_expr `(add_zero b),
  note `h none pr,
  trace_state, return ()

lemma ex2(a b c : nat) : a = b → p (f a) (f b) → p a b :=
by using_smt $ do
  intros,
  t ← tactic.to_expr `(p (f a) (f a)),
  assert `h t,  -- assert automatically closed the new goal
  trace_state,
  tactic.trace "-----",
  pr ← tactic.to_expr `(pf _ h),
  note `h2 none pr,
  trace_state,
  return ()

def foo := 0
lemma fooex : foo = 0 := rfl

lemma ex3 (a b c : nat) : a = b + foo → a + c = b + c :=
begin [smt]
  intros,
  add_fact fooex,
  ematch
end

lemma ex4 (a b c : nat) : a = b → p (f a) (f b) → p a b :=
begin [smt]
  intros,
  assert h : p (f a) (f a),
  add_fact (pf _ h)
end
