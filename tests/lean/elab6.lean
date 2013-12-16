Theorem ForallIntro2 (A : Type U) (P : A -> Bool) (H : Pi x, P x) : forall x, P x :=
        Abst (fun x, EqTIntro (H x))
