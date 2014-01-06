(*
-- The elaborator does not expand definitions marked as 'opaque'.
-- To be able to prove the following theorem, we have to unmark the
-- 'forall'
local env = get_environment()
env:set_opaque("forall", false)
*)
theorem forall::intro2 (A : (Type U)) (P : A -> Bool) (H : Pi x, P x) : forall x, P x :=
        abst (fun x, eqt::intro (H x))
