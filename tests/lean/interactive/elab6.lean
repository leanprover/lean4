(*
-- The elaborator does not expand definitions marked as 'opaque'.
-- To be able to prove the following theorem, we have to unmark the
-- 'forall'
local env = get_environment()
*)
theorem forall::intro2 (A : (Type U)) (P : A -> Bool) (H : forall x, P x) : forall x, P x :=
  H
