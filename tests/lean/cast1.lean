import cast.
import Int.

variable vector : Type -> Nat -> Type
axiom N0 (n : Nat) : n + 0 = n
theorem V0 (T : Type) (n : Nat) : (vector T (n + 0)) = (vector T n) :=
   congr (refl (vector T)) (N0 n)
variable f (n : Nat) (v : vector Int n) : Int
variable m : Nat
variable v1 : vector Int (m + 0)
-- The following application will fail because (vector Int (m + 0)) and (vector Int m)
-- are not definitionally equal.
check f m v1
-- The next one succeeds using the "casting" operator.
-- We can do it, because (V0 Int m) is a proof that
-- (vector Int (m + 0)) and (vector Int m) are propositionally equal.
-- That is, they have the same interpretation in the lean set theoretic
-- semantics.
check f m (cast (V0 Int m) v1)
