(*
simple_tac = Repeat(OrElse(conj_hyp_tac(), conj_tac(), assumption_tac()))
*)

theorem T2 (A B : Bool) : A /\ B => B /\ A :=
     Discharge (fun H : A /\ B,
                 let H1 : A := _,
                     H2 : B := _,
                     main : B /\ A := _
                 in main).
   simple_tac. done.
   simple2_tac. done.
   simple_tac. done.

print "echo command after failure"