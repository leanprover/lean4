import Std.Tactic.BVDecide

set_option trustCompiler true
/-
source: Examples/Distributed/ReliableBroadcast.lean
vc: net_byz_send_echo_vote_sent
epr: false
epr_info: not EPR: sort dependency graph has a cycle (edges: nodeset → node, node → nodeset, value → nodeset)
non_core_constants: none
standalone_check: ok
-/

open Classical in
theorem net_byz_send_echo_vote_sent
    : ∀ (node nodeset value pc_label : Type) (src th_originator : node) (th_input : value)
        (st_echoed st_voted st_delivered : node → value → Bool)
        (st_echoFrom st_voteFrom : node → value → node → Bool)
        (st_initial_net st_echo_net st_vote_net : node → node → value → Bool)
        (nset_is_byz : node → Bool) (nset_member : node → nodeset → Bool)
        (nset_is_empty nset_greater_than_third nset_supermajority : nodeset → Prop),
      (∀ (s1 s2 : nodeset),
          nset_supermajority s1 → nset_supermajority s2
            → ∃ (a_25 : node),
              nset_member a_25 s1 = Bool.true ∧ nset_member a_25 s2 = Bool.true
                ∧ ¬ nset_is_byz a_25 = Bool.true)
        → (∀ (s_4 : nodeset),
          nset_greater_than_third s_4
            → ∃ (a_27 : node), nset_member a_27 s_4 = Bool.true ∧ ¬ nset_is_byz a_27 = Bool.true)
        → (∀ (s_5 : nodeset), nset_supermajority s_5 → nset_greater_than_third s_5)
        → (∀ (s_6 : nodeset), nset_greater_than_third s_6 → ¬ nset_is_empty s_6)
        → (∀ (A B : node) (V1 V2 : value),
          ¬ nset_is_byz A = Bool.true ∧ ¬ nset_is_byz B = Bool.true ∧ st_delivered A V1 = Bool.true
              ∧ st_delivered B V2 = Bool.true
            → V1 = V2)
        → (∀ (N : node) (V : value),
          ¬ nset_is_byz th_originator = Bool.true ∧ ¬ nset_is_byz N = Bool.true
              ∧ st_delivered N V = Bool.true
            → V = th_input)
        → (∀ (D : node) (V_1 : value),
          ¬ nset_is_byz th_originator = Bool.true → st_initial_net th_originator D V_1 = Bool.true
            → V_1 = th_input)
        → (∀ (S D_1 : node) (V_2 : value),
          ¬ nset_is_byz S = Bool.true
            → st_echo_net S D_1 V_2 = Bool.true ∨ st_echoFrom D_1 V_2 S = Bool.true
            → st_echoed S V_2 = Bool.true)
        → (∀ (S_1 D_2 : node) (V_3 : value),
          ¬ nset_is_byz S_1 = Bool.true
            → st_vote_net S_1 D_2 V_3 = Bool.true ∨ st_voteFrom D_2 V_3 S_1 = Bool.true
            → st_voted S_1 V_3 = Bool.true)
        → (∀ (N_1 : node) (V1_1 V2_1 : value),
          ¬ nset_is_byz N_1 = Bool.true
            → st_echoed N_1 V1_1 = Bool.true ∧ st_echoed N_1 V2_1 = Bool.true
            → V1_1 = V2_1)
        → (∀ (N_2 : node) (V1_2 V2_2 : value),
          ¬ nset_is_byz N_2 = Bool.true
            → st_voted N_2 V1_2 = Bool.true ∧ st_voted N_2 V2_2 = Bool.true
            → V1_2 = V2_2)
        → (∀ (N_3 : node) (V_4 : value),
          ¬ nset_is_byz th_originator = Bool.true ∧ ¬ nset_is_byz N_3 = Bool.true
              ∧ st_echoed N_3 V_4 = Bool.true
            → V_4 = th_input)
        → (∀ (N_4 : node) (V_5 : value),
          ¬ nset_is_byz th_originator = Bool.true ∧ ¬ nset_is_byz N_4 = Bool.true
              ∧ st_voted N_4 V_5 = Bool.true
            → V_5 = th_input)
        → (∀ (N_5 : node) (V_6 : value),
          ¬ nset_is_byz N_5 = Bool.true → st_delivered N_5 V_6 = Bool.true
            → ∃ (q : nodeset),
              nset_supermajority q
                ∧ ∀ (s_7 : node),
                  nset_member s_7 q = Bool.true → st_voteFrom N_5 V_6 s_7 = Bool.true)
        → ∀ (pc_label_Enum_pc_start pc_label_Enum_pc_done pc_label_Enum_pc_recv2 : pc_label),
          ¬(pc_label_Enum_pc_start = pc_label_Enum_pc_done
              ∨ pc_label_Enum_pc_start = pc_label_Enum_pc_recv2)
            → ¬ pc_label_Enum_pc_done = pc_label_Enum_pc_recv2
            → (∀ (x__veil_x : pc_label),
              x__veil_x = pc_label_Enum_pc_start ∨ x__veil_x = pc_label_Enum_pc_done
                ∨ x__veil_x = pc_label_Enum_pc_recv2)
            → nset_is_byz src = Bool.true
            → ∀ (S_2 D_3 : node) (V_7 : value),
              ¬ nset_is_byz S_2 = Bool.true
                → st_vote_net S_2 D_3 V_7 = Bool.true ∨ st_voteFrom D_3 V_7 S_2 = Bool.true
                → st_voted S_2 V_7 = Bool.true := by
  epr (cegarRounds := 1000)
