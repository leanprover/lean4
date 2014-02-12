import Int.
variable P : Int -> Int -> Bool

theorem T1 (R1 : not (exists x y, P x y)) : forall x y, not (P x y) :=
         fun a b,
             (not_exists_elim (not_exists_elim R1 a)) b

axiom Ax : forall x, exists y, P x y

theorem T2 : exists x y, P x y :=
    by_contradiction (fun R : not (exists x y, P x y),
              let L1 : forall x y, not (P x y) := fun a b,
                                                         (not_exists_elim ((not_exists_elim R) a)) b,
                  L2 : exists y, P 0 y         := Ax 0
              in exists_elim L2 (fun (w : Int) (H : P 0 w),
                                    absurd H (L1 0 w))).

theorem T3 (A : (Type U)) (P : A -> A -> Bool) (a : A) (H1 : forall x, exists y, P x y) : exists x y, P x y :=
    by_contradiction (fun R : not (exists x y, P x y),
              let L1 : forall x y, not (P x y) := fun a b,
                                                   (not_exists_elim ((not_exists_elim R) a)) b,
                  L2 : exists y, P a y         :=  H1 a
              in exists_elim L2 (fun (w : A) (H : P a w),
                                    absurd H ((L1 a) w))).
