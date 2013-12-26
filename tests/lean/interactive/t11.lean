(**
auto = Repeat(OrElse(conj_hyp_tac(), conj_tac(), assumption_tac()))
**)

Theorem T2 (A B : Bool) : A /\ B -> B /\ A :=
     fun assumption : A /\ B,
          let lemma1     : A      := _,
              lemma2     : B      := _,
              conclusion : B /\ A := _
          in conclusion.
   auto. done.
   auto. done.
   auto. done.
