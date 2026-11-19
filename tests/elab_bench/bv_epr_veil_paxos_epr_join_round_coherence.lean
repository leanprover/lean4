import Std.Tactic.BVDecide
/-
source: Examples/Ivy/PaxosEPR.lean
vc: join_round_coherence
epr: true
epr_info: EPR (stratified); sort edges: quorum → node, round → quorum, value → quorum, round → node, value → node
non_core_constants: none
standalone_check: ok
-/

open Classical in
theorem join_round_coherence
    : ∀ (node value quorum round : Type) (n : node) (r : round) (th_member : node → quorum → Bool)
        (st_none : round) (st_one_a : round → Bool) (st_one_b st_left_rnd : node → round → Bool)
        (st_proposal : round → value → Bool) (st_vote st_decision : node → round → value → Bool),
      (∀ (Q1 Q2 : quorum), ∃ (N : node), th_member N Q1 = Bool.true ∧ th_member N Q2 = Bool.true)
        → ∀ (tot_le : round → round → Prop),
          (∀ (x_1 : round), tot_le x_1 x_1)
            → (∀ (x_2 y_1 z : round), tot_le x_2 y_1 → tot_le y_1 z → tot_le x_2 z)
            → (∀ (x_3 y_2 : round), tot_le x_3 y_2 → tot_le y_2 x_3 → x_3 = y_2)
            → (∀ (x_4 y_3 : round), tot_le x_4 y_3 ∨ tot_le y_3 x_4)
            → (∀ (N1 : node) (R1 : round) (V1 : value) (N2 : node) (R2 : round) (V2 : value),
              st_decision N1 R1 V1 = Bool.true ∧ st_decision N2 R2 V2 = Bool.true → V1 = V2)
            → (∀ (R : round) (V1_1 V2_1 : value),
              st_proposal R V1_1 = Bool.true ∧ st_proposal R V2_1 = Bool.true → V1_1 = V2_1)
            → (∀ (N_1 : node) (R_1 : round) (V : value),
              st_vote N_1 R_1 V = Bool.true → st_proposal R_1 V = Bool.true)
            → (∀ (R_2 : round) (V_1 : value),
              (∃ (n_1 : node), st_decision n_1 R_2 V_1 = Bool.true)
                → ∃ (q : quorum), ∀ (N_2 : node),
                  th_member N_2 q = Bool.true → st_vote N_2 R_2 V_1 = Bool.true)
            → (∀ (N_3 : node) (V_2 : value), ¬ st_vote N_3 st_none V_2 = Bool.true)
            → (∀ (R1_1 R2_1 : round) (V1_2 V2_2 : value) (Q : quorum),
              ¬ tot_le R2_1 R1_1 ∧ st_proposal R2_1 V2_2 = Bool.true ∧ V1_2 ≠ V2_2
                → ∃ (n_2 : node),
                  th_member n_2 Q = Bool.true ∧ st_left_rnd n_2 R1_1 = Bool.true
                    ∧ ¬ st_vote n_2 R1_1 V1_2 = Bool.true)
            → (∀ (N_4 : node) (R2_2 R1_2 : round),
              st_one_b N_4 R2_2 = Bool.true ∧ ¬ tot_le R2_2 R1_2 → st_left_rnd N_4 R1_2 = Bool.true)
            → ¬ r = st_none → st_one_a r = Bool.true → ¬ st_left_rnd n r = Bool.true
            → ∀ (maxr : round) (v : value),
              ((maxr = st_none
                    ∧ ∀ (mAXR : round) (v' : value),
                      ¬(¬ tot_le r mAXR ∧ st_vote n mAXR v' = Bool.true))
                  ∨ ¬ maxr = st_none ∧ ¬ tot_le r maxr ∧ st_vote n maxr v = Bool.true
                    ∧ ∀ (mAXR_1 : round) (v'_1 : value),
                      ¬ tot_le r mAXR_1 → st_vote n mAXR_1 v'_1 = Bool.true → tot_le mAXR_1 maxr)
                → ∀ (N1_1 : node) (R1_3 : round) (V1_3 : value) (N2_1 : node) (R2_3 : round)
                    (V2_3 : value),
                  st_decision N1_1 R1_3 V1_3 = Bool.true → st_decision N2_1 R2_3 V2_3 = Bool.true
                    → V1_3 = V2_3 := by
  epr (cegarRounds := 1000)
