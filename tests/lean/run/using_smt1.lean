open smt_tactic tactic

example (a b c : nat) : a = c → a = b → b = c :=
by using_smt close

set_option pp.all true

example (a b c : nat) : a > nat.zero → a = c → a = b → b = c :=
by using_smt (trace_state >> close)

example (p q r : Prop) : p → q → ¬p → r :=
by using_smt (trace_state >> close)

example (a b c : nat) : a > nat.zero → 0 < a :=
by using_smt $ return ()

example (a b c d : nat) : a ≠ d → a = b ∧ b = c → a = c :=
by using_smt $ return ()

set_option pp.all false

example (f : nat → nat) (a b c : nat) :
        f a = 0 →
        f b = 1 →
        f a = f b ∨ f a = c →
        c = 0 :=
by using_smt $ return()

example (f : nat → nat) (a b c d e: nat) :
        f a = 0 →
        f a = d →
        f b = e →
        f b = 1 →
        d = e ∨ f a = c →
        c = 0 :=
by using_smt $ return()

example (f : bool → bool) (a b c : bool) :
        f a = ff →
        f b = tt →
        f a = f b ∨ f a = c →
        c = ff :=
by using_smt $ return()

example (f : list nat → list nat) (a b c : list nat) :
        f a = [] →
        f b = [0, 1] →
        f a = f b ∨ f a = c →
        c = [] :=
by using_smt $ return()
