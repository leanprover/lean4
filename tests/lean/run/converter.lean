open tactic conv
open tactic

run_cmd mk_simp_attr `foo
run_cmd mk_simp_attr `bla

constant f : nat → nat → nat
@[foo] lemma f_lemma : ∀ x, f x x = 0 :=
sorry

constant g : nat → nat
@[bla] lemma g_lemma : ∀ x, g x = x :=
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

@[simp] lemma sizeof_nat_eq (n : ℕ) : sizeof n = n := rfl

example (a b c : nat) : (λ x, g (f x (sizeof x))) = (λ x, 0) :=
by conversion $
  funext $ do
    trace_lhs,
    apply_simp_set `bla,
    dsimp,
    apply_simp_set `foo

constant h : nat → nat → nat

lemma ex (a : nat) : (λ a, h (f a (sizeof a)) (g a)) = (λ a, h 0 a) :=
by conversion $
   bottom_up $
     (apply_simp_set `foo <|> apply_simp_set `bla <|> dsimp)

lemma ex2 {A : Type} [comm_group A] (a b : A) : b * 1 * a = a * b :=
by conversion $
   bottom_up (apply_simp_set `default)

lemma ex3 (p q r : Prop) : (p ∧ true ∧ p) = p :=
by conversion $
   bottom_up (apply_propext_simp_set `default)

#print "---------"

lemma ex4 (a b c : nat) : g (g (g (f (f (g (g a)) (g (g a))) a))) = g (g (g (f (f a a) a))) :=
by conversion $
   findp `(λ x, f (g x) (g x)) $
     trace "found pattern" >> trace_lhs >>
     bottom_up (apply_simp_set `bla)

lemma ex5 (a b c : nat) : g (g (g (f (f (g (g a)) (g (g a))) a))) = g (g (g (f (f a a) a))) :=
by conversion $
   find $
     match_expr `(λ x, f (g x) (g x)) >>
     trace "found pattern" >> trace_lhs >>
     bottom_up (apply_simp_set `bla)
