(**
-- Define a simple tactic using Lua
auto = REPEAT(ORELSE(assumption_tac, conj_tac, conj_hyp_tac))
**)

Theorem T1 (A B : Bool) : A /\ B -> B /\ A :=
     fun assumption : A /\ B,
          let lemma1 := (show A by auto),
              lemma2 := (show B by auto)
          in (show B /\ A by auto)

Show Environment 1.
