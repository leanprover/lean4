(**
-- The elaborator does not expand definitions marked as 'hidden'.
-- To be able to prove the following theorem, we have to unmark the
-- 'forall'
local env = get_environment()
set_hidden_flag(env, "forall", false)
**)
Theorem ForallIntro2 (A : (Type U)) (P : A -> Bool) (H : Pi x, P x) : forall x, P x :=
        Abst (fun x, EqTIntro (H x))
