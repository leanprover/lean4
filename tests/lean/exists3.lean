import Int.
variable P : Int -> Int -> Bool

set::opaque exists false.

theorem T1 (R1 : not (exists x y, P x y)) : forall x y, not (P x y) :=
         forall::intro (fun a,
             forall::intro (fun b,
                 forall::elim (not::not::elim (forall::elim (not::not::elim R1) a)) b))

axiom Ax : forall x, exists y, P x y

theorem T2 : exists x y, P x y :=
    refute (fun R : not (exists x y, P x y),
              let L1 : forall x y, not (P x y) := forall::intro (fun a,
                                                     forall::intro (fun b,
                                                         forall::elim (not::not::elim (forall::elim (not::not::elim R) a)) b)),
                  L2 : exists y, P 0 y         := forall::elim Ax 0
              in exists::elim L2 (fun (w : Int) (H : P 0 w),
                                    absurd H (forall::elim (forall::elim L1 0) w))).

theorem T3 (A : (Type U)) (P : A -> A -> Bool) (a : A) (H1 : forall x, exists y, P x y) : exists x y, P x y :=
    refute (fun R : not (exists x y, P x y),
              let L1 : forall x y, not (P x y) := forall::intro (fun a,
                                                     forall::intro (fun b,
                                                         forall::elim (not::not::elim (forall::elim (not::not::elim R) a)) b)),
                  L2 : exists y, P a y         := forall::elim H1 a
              in exists::elim L2 (fun (w : A) (H : P a w),
                                    absurd H (forall::elim (forall::elim L1 a) w))).
