import Int.
definition double {A : Type} (f : A -> A) : A -> A := fun x, f (f x).
definition big {A : Type} (f : A -> A) : A -> A := (double (double (double (double (double (double (double f))))))).

(*

 -- Tactic for trying to prove goal using Reflexivity, Congruence and available assumptions
local congr_tac = Repeat(OrElse(apply_tac("refl"), apply_tac("congr"), assumption_tac()))

-- Create an eager tactic that only tries to prove goal after unfolding everything
eager_tac = Then(-- unfold homogeneous equality
                 Try(unfold_tac("eq")),
                 -- keep unfolding defintions above and beta-reducing
                 Repeat(unfold_tac() .. Repeat(beta_tac())),
                 congr_tac)

-- The 'lazy' version tries first to prove without unfolding anything
lazy_tac = OrElse(Then(Try(unfold_tac("eq")), congr_tac, now_tac()),
                  eager_tac)

*)

exit -- temporarily disable the follwoing tests

theorem T1 (a b : Int) (f : Int -> Int) (H : a = b) : (big f a) = (big f b).
        eager_tac.
        done.

theorem T2 (a b : Int) (f : Int -> Int) (H : a = b) : (big f a) = (big f b).
        lazy_tac.
        done.

theorem T3 (a b : Int) (f : Int -> Int) (H : a = b) : (big f a) = ((double (double (double (double (double (double (double f))))))) b).
        lazy_tac.
        done.
