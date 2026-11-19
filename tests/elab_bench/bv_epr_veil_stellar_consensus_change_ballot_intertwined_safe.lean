import Std.Tactic.BVDecide
/-
source: Examples/StellarConsensus/SCP.lean
vc: change_ballot_intertwined_safe
epr: false
epr_info: not EPR: sort dependency graph has a cycle (edges: ballot → ballot, nset → node, ballot → nset, value → nset, ballot → node, value → node)
non_core_constants: none
standalone_check: ok
-/

open Classical in
theorem change_ballot_intertwined_safe
    : ∀ (value node nset ballot : Type) (n : node) (b : ballot)
        (st_accepted_prepared st_confirmed_prepared st_accepted_committed st_confirmed_committed
          : node → ballot → value → Bool)
        (st_nomination_output : node → value → Bool)
        (st_started st_left_ballot : node → ballot → Bool)
        (st_received_accept_prepare st_received_accept_commit : node → node → ballot → value → Bool)
        (tot_le : ballot → ballot → Prop),
      (∀ (x_1 : ballot), tot_le x_1 x_1)
        → (∀ (x_2 y_1 z : ballot), tot_le x_2 y_1 → tot_le y_1 z → tot_le x_2 z)
        → (∀ (x_3 y_2 : ballot), tot_le x_3 y_2 → tot_le y_2 x_3 → x_3 = y_2)
        → (∀ (x_4 y_3 : ballot), tot_le x_4 y_3 ∨ tot_le y_3 x_4)
        → ∀ (tot_lt : ballot → ballot → Prop),
          (∀ (x_6 y_5 : ballot), tot_lt x_6 y_5 ↔ tot_le x_6 y_5 ∧ x_6 ≠ y_5)
            → ∀ (tot_next : ballot → ballot → Prop),
              (∀ (x_8 y_7 : ballot),
                  tot_next x_8 y_7
                    ↔ tot_lt x_8 y_7 ∧ ∀ (z_1 : ballot), tot_lt x_8 z_1 → tot_le y_7 z_1)
                → ∀ (tot_zero : ballot),
                  (∀ (x_9 : ballot), tot_le tot_zero x_9)
                    → ∀ (bg_well_behaved bg_intertwined bg_intact : node → Prop)
                        (bg_member : node → nset → Prop) (bg_is_quorum : nset → Prop),
                      (∀ (n_1 : node), bg_intact n_1 → bg_intertwined n_1)
                        → (∀ (n_2 : node), bg_intertwined n_2 → bg_well_behaved n_2)
                        → (∀ (q1 q2 : nset),
                          ((∃ (n1 : node), bg_intertwined n1 ∧ bg_is_quorum q1 ∧ bg_member n1 q1)
                              ∧ ∃ (n2 : node),
                                bg_intertwined n2 ∧ bg_is_quorum q2 ∧ bg_member n2 q2)
                            → ∃ (n3 : node), bg_well_behaved n3 ∧ bg_member n3 q1 ∧ bg_member n3 q2)
                        → (∀ (n1_1 n2_1 : node) (b1 b2 : ballot) (v1 v2 : value),
                          bg_intertwined n1_1 ∧ bg_intertwined n2_1
                              ∧ st_confirmed_committed n1_1 b1 v1 = Bool.true
                              ∧ st_confirmed_committed n2_1 b2 v2 = Bool.true
                            → v1 = v2)
                        → (∀ (N : node) (B : ballot) (V : value),
                          bg_well_behaved N ∧ st_accepted_committed N B V = Bool.true
                            → st_confirmed_prepared N B V = Bool.true)
                        → (∀ (N_1 : node) (B1 B2 : ballot) (V1 V2 : value),
                          bg_well_behaved N_1 ∧ st_accepted_prepared N_1 B2 V2 = Bool.true
                              ∧ tot_lt B1 B2 ∧ V1 ≠ V2
                            → ¬ st_accepted_committed N_1 B1 V1 = Bool.true)
                        → (∀ (B_1 : ballot) (V_1 : value),
                          (∃ (N_2 : node),
                              bg_intertwined N_2 ∧ st_confirmed_committed N_2 B_1 V_1 = Bool.true)
                            → ∃ (Q : nset),
                              bg_is_quorum Q
                                ∧ (∃ (N_3 : node), bg_intertwined N_3 ∧ bg_member N_3 Q)
                                ∧ ∀ (N_4 : node),
                                  bg_well_behaved N_4 ∧ bg_member N_4 Q
                                    → st_accepted_committed N_4 B_1 V_1 = Bool.true)
                        → (∀ (B_2 : ballot) (V_2 : value),
                          (∃ (N_5 : node),
                              bg_intertwined N_5 ∧ st_confirmed_prepared N_5 B_2 V_2 = Bool.true)
                            → ∃ (Q_1 : nset),
                              bg_is_quorum Q_1
                                ∧ (∃ (N_6 : node), bg_intertwined N_6 ∧ bg_member N_6 Q_1)
                                ∧ ∀ (N_7 : node),
                                  bg_well_behaved N_7 ∧ bg_member N_7 Q_1
                                    → st_accepted_prepared N_7 B_2 V_2 = Bool.true)
                        → (∀ (N_8 N2 : node) (B_3 : ballot) (V_3 : value),
                          bg_well_behaved N_8 ∧ st_received_accept_commit N_8 N2 B_3 V_3 = Bool.true
                              ∧ bg_well_behaved N2
                            → st_accepted_committed N2 B_3 V_3 = Bool.true)
                        → (∀ (N_9 N2_1 : node) (B_4 : ballot) (V_4 : value),
                          bg_well_behaved N_9
                              ∧ st_received_accept_prepare N_9 N2_1 B_4 V_4 = Bool.true
                              ∧ bg_well_behaved N2_1
                            → st_accepted_prepared N2_1 B_4 V_4 = Bool.true)
                        → (∀ (N_10 : node) (B_5 : ballot) (V1_1 V2_1 : value),
                          bg_well_behaved N_10 ∧ st_accepted_prepared N_10 B_5 V1_1 = Bool.true
                              ∧ st_accepted_prepared N_10 B_5 V2_1 = Bool.true
                            → V1_1 = V2_1)
                        → ¬ st_left_ballot n b = Bool.true → ¬ st_started n b = Bool.true
                        → ∀ (bmax : ballot) (vmax : value),
                          ((∀ (B_6 : ballot) (V_5 : value),
                                  tot_lt B_6 b → ¬ st_confirmed_prepared n B_6 V_5 = Bool.true)
                                ∧ st_nomination_output n vmax = Bool.true
                              ∨ tot_lt bmax b ∧ st_confirmed_prepared n bmax vmax = Bool.true
                                ∧ ∀ (B_7 : ballot) (V_6 : value),
                                  tot_lt B_7 b → st_confirmed_prepared n B_7 V_6 = Bool.true
                                    → tot_le B_7 bmax)
                            → ∀ (n1_2 n2_2 : node) (b1_1 b2_1 : ballot) (v1_1 v2_1 : value),
                              bg_intertwined n1_2 → bg_intertwined n2_2
                                → st_confirmed_committed n1_2 b1_1 v1_1 = Bool.true
                                → st_confirmed_committed n2_2 b2_1 v2_1 = Bool.true
                                → v1_1 = v2_1 := by
  epr (cegarRounds := 1000)
