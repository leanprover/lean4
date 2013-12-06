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
   apply simple2_tac. done.
   apply simple_tac. done.

Echo "echo command after failure"