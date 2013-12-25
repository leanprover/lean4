Theorem T (A : Type) (p : A -> Bool) (f : A -> A -> A) : forall x y z, p (f x x) => x = y => x = z => p (f y z).
   apply ForallIntro.
   apply beta_tac.
   apply ForallIntro.
   apply beta_tac.
   apply ForallIntro.
   apply beta_tac.
   apply Discharge.
   apply Discharge.
   apply Discharge.
   apply (Subst (Subst H H::1) H::2)
   done.

Show Environment 1.