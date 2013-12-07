Definition double {A : Type} (f : A -> A) : A -> A := fun x, f (f x).
Definition big {A : Type} (f : A -> A) : A -> A := (double (double (double (double (double (double (double f))))))).

(**

 -- Tactic for trying to prove goal using Reflexivity, Congruence and available assumptions
local congr_tac = REPEAT(ORELSE(apply_tac("Refl"), apply_tac("Congr"), assumption_tac))

-- Create an eager tactic that only tries to prove goal after unfolding everything
eager_tac = THEN(-- unfold homogeneous equality
                 TRY(unfold_tac("eq")),
                 -- keep unfolding defintions above and beta-reducing
                 REPEAT(unfold_tac .. REPEAT(beta_tac)),
                 congr_tac)

-- The 'lazy' version tries first to prove without unfolding anything
lazy_tac = ORELSE(THEN(TRY(unfold_tac("eq")), congr_tac, now_tac),
                  eager_tac)

**)

Theorem T1 (a b : Int) (f : Int -> Int) (H : a = b) : (big f a) = (big f b).
        apply eager_tac.
        done.

Theorem T2 (a b : Int) (f : Int -> Int) (H : a = b) : (big f a) = (big f b).
        apply lazy_tac.
        done.

Theorem T3 (a b : Int) (f : Int -> Int) (H : a = b) : (big f a) = ((double (double (double (double (double (double (double f))))))) b).
        apply lazy_tac.
        done.
