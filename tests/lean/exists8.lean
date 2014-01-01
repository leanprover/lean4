Import Int.
Variable P : Int -> Int -> Bool

Theorem T1 (R1 : not (exists x y, P x y)) : forall x y, not (P x y) :=
         ForallIntro (fun a,
             ForallIntro (fun b,
                 ForallElim (NotExistsElim (ForallElim (NotExistsElim R1) a)) b))

Axiom Ax : forall x, exists y, P x y

Theorem T2 : exists x y, P x y :=
    Refute (fun R : not (exists x y, P x y),
              let L1 : forall x y, not (P x y) := ForallIntro (fun a,
                                                     ForallIntro (fun b,
                                                         ForallElim (NotExistsElim (ForallElim (NotExistsElim R) a)) b)),
                  L2 : exists y, P 0 y         := ForallElim Ax 0
              in ExistsElim L2 (fun (w : Int) (H : P 0 w),
                                    Absurd H (ForallElim (ForallElim L1 0) w))).

Theorem T3 (A : (Type U)) (P : A -> A -> Bool) (a : A) (H1 : forall x, exists y, P x y) : exists x y, P x y :=
    Refute (fun R : not (exists x y, P x y),
              let L1 : forall x y, not (P x y) := ForallIntro (fun a,
                                                     ForallIntro (fun b,
                                                         ForallElim (NotExistsElim (ForallElim (NotExistsElim R) a)) b)),
                  L2 : exists y, P a y         := ForallElim H1 a
              in ExistsElim L2 (fun (w : A) (H : P a w),
                                    Absurd H (ForallElim (ForallElim L1 a) w))).
