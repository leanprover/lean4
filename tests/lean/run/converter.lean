open tactic conv
open tactic

run_command mk_simp_attr `foo
run_command mk_simp_attr `bla

constant f : nat → nat → nat
@[foo] def f_lemma : ∀ x, f x x = 0 :=
sorry

constant g : nat → nat
@[bla] def g_lemma : ∀ x, g x = x :=
sorry

example (a b c : nat) : (λ x, g (f (a + 0) (sizeof x))) a = 0 :=
by conversion $
  whnf >>
  trace_lhs >>
  apply_simp_set `bla >>
  dsimp >>
  trace "after defeq simplifier" >>
  trace_lhs >>
  change `(f a a) >>
  trace_lhs >>
  apply_simp_set `foo >>
  trace_lhs

set_option trace.app_builder true

example (a b c : nat) : (λ x, g (f x (sizeof x))) = (λ x, 0) :=
by conversion $
  funext $ do
    trace_lhs,
    apply_simp_set `bla,
    dsimp,
    apply_simp_set `foo
