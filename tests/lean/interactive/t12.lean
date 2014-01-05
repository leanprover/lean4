(*
import("tactic.lua")
-- Define a simple tactic using Lua
auto = Repeat(OrElse(assumption_tac(), conj_tac(), conj_hyp_tac()))
*)

Theorem T1 (A B : Bool) : A /\ B -> B /\ A :=
     fun assumption : A /\ B,
          let lemma1     : A      := (by auto),
              lemma2     : B      := (by auto)
          in (show B /\ A by auto)

Show Environment 1. -- Show proof for the previous theorem

Theorem T2 (A B : Bool) : A /\ B -> B /\ A :=
     fun assumption : A /\ B,
          let lemma1     : A      := _,
              lemma2     : B      := _
          in _.
   auto. done.
   auto. done.
   auto. done.

Theorem T3 (A B : Bool) : A /\ B -> B /\ A :=
     fun assumption : A /\ B,
          let lemma1     : A      := _,
              lemma2     : B      := _
          in _.
   conj_hyp. exact. done.
   conj_hyp. exact. done.
   apply Conj. exact. done.

Theorem T4 (A B : Bool) : A /\ B -> B /\ A :=
     fun assumption : A /\ B,
          let lemma1     : A      := _,
              lemma2     : B      := _
          in (show B /\ A by auto).
   conj_hyp. exact. done.
   conj_hyp. exact. done.
