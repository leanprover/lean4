(* import("macros.lua") *)

Theorem T (A : Type) (p : A -> Bool) (f : A -> A -> A) : forall x y z, p (f x x) => x = y => x = z => p (f y z) :=
   take x y z, Assume (H1 : p (f x x)) (H2 : x = y) (H3 : x = z),
      Subst' H1 H2 H3.

print Environment 1.