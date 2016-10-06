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

constant h : nat → nat → nat

meta def conv.depth : conv unit → conv unit
| c r e :=
  (subc (conv.depth c) >> repeat c) r e

lemma ex (a : nat) : (λ a, h (f a (sizeof a)) (g a)) = (λ a, h 0 a) :=
by conversion $
   depthfirst $
     (apply_simp_set `foo <|> apply_simp_set `bla <|> dsimp)

lemma ex2 {A : Type} [comm_group A] (a b : A) : b * 1 * a = a * b :=
by conversion $
   depthfirst (apply_simp_set `default)

lemma ex3 (p q r : Prop) : (p ∧ true ∧ p) = p :=
by conversion $
   depthfirst (apply_propext_simp_set `default)

lemma ex4 (a b c : nat) : g (g (g (f (f (g a) (g a)) a))) = g (g (g (f (f a a) a))) :=
by do
   trace "---------",
   conversion $
   depthfirst (match_expr `(λ x, f (g x) (g x)) >> depthfirst (apply_simp_set `bla))
