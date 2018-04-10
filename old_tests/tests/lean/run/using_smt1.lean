open smt_tactic tactic

lemma ex1 (a b c : nat) : a = c → a = b → b = c :=
by using_smt intros

set_option pp.all true

lemma ex2 (a b c : nat) : a > nat.zero → a = c → a = b → b = c :=
by using_smt intros

lemma ex3 (p q r : Prop) : p → q → ¬p → r :=
by using_smt intros

lemma ex4 (a b c : nat) : a > nat.zero → 0 < a :=
by simp [(>)]; using_smt intros

lemma ex5 (a b c d : nat) : a ≠ d → a = b ∧ b = c → a = c :=
by using_smt intros

set_option pp.all false

lemma ex6 (f : nat → nat) (a b c : nat) :
        f a = 0 →
        f b = 1 →
        f a = f b ∨ f a = c →
        c = 0 :=
by using_smt intros

lemma ex7 (f : nat → nat) (a b c d e: nat) :
        f a = 0 →
        f a = d →
        f b = e →
        f b = 1 →
        d = e ∨ f a = c →
        c = 0 :=
by using_smt intros

lemma ex8 (f : bool → bool) (a b c : bool) :
        f a = ff →
        f b = tt →
        f a = f b ∨ f a = c →
        c = ff :=
by using_smt intros

lemma ex9 (f : list nat → list nat) (a b c : list nat) :
        f a = [] →
        f b = [0, 1] →
        f a = f b ∨ f a = c →
        c = [] :=
by using_smt intros

lemma ex10 (a b c d e : int) : a = b → b ≠ c → (a = c ∨ d = e) → d = e :=
by using_smt intros
