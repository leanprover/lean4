(*
-- The elaborator does not expand definitions marked as 'opaque'.
-- To be able to prove the following theorem, we have to unmark the
-- 'forall'
local env = get_environment()
env:set_opaque("forall", false)
*)
theorem ForallIntro2 (A : (Type U)) (P : A -> Bool) (H : Pi x, P x) : forall x, P x :=
        Abst (fun x, EqTIntro (H x))
