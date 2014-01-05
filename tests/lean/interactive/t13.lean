(*
-- Define a simple tactic using Lua
auto = Repeat(OrElse(assumption_tac(), conj_tac(), conj_hyp_tac()))
*)

Theorem T1 (A B : Bool) : A /\ B -> B /\ A :=
     fun assumption : A /\ B,
          let lemma1 := (have A by auto),
              lemma2 := (have B by auto)
          in (have B /\ A by auto)

print Environment 1.
