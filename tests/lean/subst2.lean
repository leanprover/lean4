(* import("tactic.lua") *)
theorem T (A : Type) (p : A -> Bool) (f : A -> A -> A) : forall x y z, p (f x x) → x = y → x = z → p (f y z).
   apply (subst (subst H H::1) H::2)
   done.

print environment 1.