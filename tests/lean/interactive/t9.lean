Theorem T1 (A B : Bool) : A /\ B => B /\ A :=
     Discharge (fun H : A /\ B,
                   let main : B /\ A :=
                       (let H1 : B := _,
                            H2 : A := _
                        in _)
                   in main).
  apply conj_hyp_tac.
  assumption.
  done.
  apply conj_hyp_tac.
  assumption.
  done.
  apply Conj.
  assumption.
  done.

(**
simple_tac = REPEAT(ORELSE(conj_hyp_tac, conj_tac, assumption_tac))
**)

Theorem T2 (A B : Bool) : A /\ B => B /\ A :=
     Discharge (fun H : A /\ B,
                 let H1 : A := _,
                     H2 : B := _,
                     main : B /\ A := _
                 in main).
   apply simple_tac. done.
   apply simple_tac. done.
   apply simple_tac. done.
