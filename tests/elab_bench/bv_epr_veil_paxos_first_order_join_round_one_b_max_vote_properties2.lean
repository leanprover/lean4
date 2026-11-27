import Std.Tactic.BVDecide
/-
source: Examples/Ivy/PaxosFirstOrder.lean
vc: join_round_one_b_max_vote_properties2
epr: false
epr_info: not EPR: sort dependency graph has a cycle (edges: quorum → node, round → quorum, value → quorum, round → node, value → node, round → round, value → round, quorum → round, round → value, value → value, quorum → value)
non_core_constants: none
standalone_check: ok
-/

open Classical in
theorem join_round_one_b_max_vote_properties2
    : ∀ (node value quorum round : Type) (n : node) (r : round) (th_member : node → quorum → Bool)
        (st_none : round) (st_one_a : round → Bool)
        (st_one_b_max_vote : node → round → round → value → Bool)
        (st_proposal : round → value → Bool) (st_vote st_decision : node → round → value → Bool),
      (∀ (Q1 Q2 : quorum), ∃ (N : node), th_member N Q1 = Bool.true ∧ th_member N Q2 = Bool.true)
        → ∀ (node_inhabited : node) (value_inhabited : value) (quorum_inhabited : quorum)
            (round_inhabited : round) (tot_le : round → round → Prop),
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
              (∃ (N_2 : node), st_decision N_2 R_2 V_1 = Bool.true)
                → ∃ (Q : quorum), ∀ (N_3 : node),
                  th_member N_3 Q = Bool.true → st_vote N_3 R_2 V_1 = Bool.true)
            → (∀ (N_4 : node) (R2_1 : round) (V1_2 : value) (R1_1 : round) (V2_2 : value),
              st_one_b_max_vote N_4 R2_1 st_none V1_2 = Bool.true ∧ ¬ tot_le R2_1 R1_1
                → ¬ st_vote N_4 R1_1 V2_2 = Bool.true)
            → (∀ (N_5 : node) (R_3 RMAX : round) (V_2 : value),
              st_one_b_max_vote N_5 R_3 RMAX V_2 = Bool.true ∧ RMAX ≠ st_none
                → ¬ tot_le R_3 RMAX ∧ st_vote N_5 RMAX V_2 = Bool.true)
            → (∀ (N_6 : node) (R_4 RMAX_1 : round) (V_3 : value) (ROTHER : round) (VOTHER : value),
              st_one_b_max_vote N_6 R_4 RMAX_1 V_3 = Bool.true ∧ RMAX_1 ≠ st_none
                  ∧ ¬ tot_le R_4 ROTHER ∧ ¬ tot_le ROTHER RMAX_1
                → ¬ st_vote N_6 ROTHER VOTHER = Bool.true)
            → (∀ (N_7 : node) (V_4 : value), ¬ st_vote N_7 st_none V_4 = Bool.true)
            → (∀ (R1_2 R2_2 : round) (V1_3 V2_3 : value) (Q_1 : quorum),
              ¬ tot_le R2_2 R1_2 ∧ st_proposal R2_2 V2_3 = Bool.true ∧ V1_3 ≠ V2_3
                → ∃ (N_8 : node), ∃ (R3 : round), ∃ (RMAX_2 : round), ∃ (V_5 : value),
                  th_member N_8 Q_1 = Bool.true ∧ ¬ tot_le R3 R1_2
                    ∧ st_one_b_max_vote N_8 R3 RMAX_2 V_5 = Bool.true
                    ∧ ¬ st_vote N_8 R1_2 V1_3 = Bool.true)
            → ¬ r = st_none → st_one_a r = Bool.true
            → (∀ (x_5 x_6 : round) (x_7 : value),
              ¬(st_one_b_max_vote n x_5 x_6 x_7 = Bool.true ∧ ¬ tot_le x_5 r))
            → ∀ (maxr : round) (v : value),
              ((maxr = st_none
                    ∧ ∀ (mAXR : round) (v' : value),
                      ¬(¬ tot_le r mAXR ∧ st_vote n mAXR v' = Bool.true))
                  ∨ ¬ maxr = st_none ∧ ¬ tot_le r maxr ∧ st_vote n maxr v = Bool.true
                    ∧ ∀ (mAXR_1 : round) (v'_1 : value),
                      ¬ tot_le r mAXR_1 → st_vote n mAXR_1 v'_1 = Bool.true → tot_le mAXR_1 maxr)
                → ∀ (N_9 : node) (R_5 RMAX_3 : round) (V_6 : value),
                  (¬(n = N_9 ∧ r = R_5 ∧ maxr = RMAX_3 ∧ v = V_6)
                      → st_one_b_max_vote N_9 R_5 RMAX_3 V_6 = Bool.true)
                    → RMAX_3 ≠ st_none
                    → ¬ tot_le R_5 RMAX_3 ∧ st_vote N_9 RMAX_3 V_6 = Bool.true := by
  epr (cegarRounds := 1000)
