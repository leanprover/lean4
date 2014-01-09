(*
import("tactic.lua")
-- Define a simple tactic using Lua
auto = Repeat(OrElse(assumption_tac(), conj_tac(), conj_hyp_tac()))
*)

theorem T1 (A B : Bool) : A /\ B -> B /\ A :=
     fun assumption : A /\ B,
          let lemma1     : A      := (by auto),
              lemma2     : B      := (by auto)
          in (have B /\ A by auto)

print environment 1. -- print proof for the previous theorem

theorem T2 (A B : Bool) : A /\ B -> B /\ A :=
     fun assumption : A /\ B,
          let lemma1     : A      := _,
              lemma2     : B      := _
          in _.
   auto. done.
   auto. done.
   auto. done.

theorem T3 (A B : Bool) : A /\ B -> B /\ A :=
     fun assumption : A /\ B,
          let lemma1     : A      := _,
              lemma2     : B      := _
          in _.
   conj_hyp. exact. done.
   conj_hyp. exact. done.
   apply and_intro. exact. done.

theorem T4 (A B : Bool) : A /\ B -> B /\ A :=
     fun assumption : A /\ B,
          let lemma1     : A      := _,
              lemma2     : B      := _
          in (have B /\ A by auto).
   conj_hyp. exact. done.
   conj_hyp. exact. done.
