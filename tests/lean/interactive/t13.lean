(*
-- Define a simple tactic using Lua
auto = Repeat(OrElse(assumption_tac(), conj_tac(), conj_hyp_tac()))
*)

theorem T1 (A B : Bool) : A /\ B -> B /\ A :=
     fun assumption : A /\ B,
          let lemma1 := (show A, by auto),
              lemma2 := (show B, by auto)
          in (show B /\ A, by auto)

print environment 1.
