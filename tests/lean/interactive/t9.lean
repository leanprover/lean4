(* import("tactic.lua") *)
Theorem T1 (A B : Bool) : A /\ B => B /\ A :=
     Discharge (fun H : A /\ B,
                   let main : B /\ A :=
                       (let H1 : B := _,
                            H2 : A := _
                        in _)
                   in main).
  conj_hyp.
  exact.
  done.
  conj_hyp.
  exact.
  done.
  apply Conj.
  exact.
  done.

(*
simple_tac = Repeat(OrElse(conj_hyp_tac(), conj_tac(), assumption_tac()))
*)

Theorem T2 (A B : Bool) : A /\ B => B /\ A :=
     Discharge (fun H : A /\ B,
                 let H1 : A := _,
                     H2 : B := _,
                     main : B /\ A := _
                 in main).
   simple_tac. done.
   simple_tac. done.
   simple_tac. done.
