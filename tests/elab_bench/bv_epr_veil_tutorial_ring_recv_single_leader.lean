import Std.Tactic.BVDecide

set_option trustCompiler true
/-
source: Examples/Tutorial/Ring.lean
vc: recv_single_leader
epr: true
epr_info: EPR (stratified); sort edges: none
non_core_constants: none
standalone_check: ok
-/

open Classical in
theorem recv_single_leader
    : ∀ (node : Type) (sender n next : node) (st_leader : node → Bool)
        (st_pending : node → node → Bool) (tot_le : node → node → Prop),
      (∀ (x_1 : node), tot_le x_1 x_1)
        → (∀ (x_2 y_1 z : node), tot_le x_2 y_1 → tot_le y_1 z → tot_le x_2 z)
        → (∀ (x_3 y_2 : node), tot_le x_3 y_2 → tot_le y_2 x_3 → x_3 = y_2)
        → (∀ (x_4 y_3 : node), tot_le x_4 y_3 ∨ tot_le y_3 x_4)
        → ∀ (btwn_btw : node → node → node → Prop),
          (∀ (x_6 y_5 z_2 : node), btwn_btw x_6 y_5 z_2 → btwn_btw y_5 z_2 x_6)
            → (∀ (w x_7 y_6 z_3 : node),
              btwn_btw w x_7 y_6 → btwn_btw w y_6 z_3 → btwn_btw w x_7 z_3)
            → (∀ (w_1 x_8 y_7 : node), btwn_btw w_1 x_8 y_7 → ¬ btwn_btw w_1 y_7 x_8)
            → (∀ (w_2 x_9 y_8 : node),
              btwn_btw w_2 x_9 y_8 ∨ btwn_btw w_2 y_8 x_9 ∨ w_2 = x_9 ∨ w_2 = y_8 ∨ x_9 = y_8)
            → (∀ (L1 L2 : node), st_leader L1 = Bool.true ∧ st_leader L2 = Bool.true → L1 = L2)
            → (∀ (L N : node), st_leader L = Bool.true → tot_le N L)
            → (∀ (L_1 N_1 : node), st_pending L_1 L_1 = Bool.true → tot_le N_1 L_1)
            → (∀ (S D N_2 : node), st_pending S D = Bool.true ∧ btwn_btw S N_2 D → tot_le N_2 S)
            → ¬ n = next → (∀ (N' : node), ¬ N' = n → ¬ N' = next → ¬ btwn_btw n N' next)
            → st_pending sender n = Bool.true
            → ∀ (b : Bool),
              (b = Bool.true) = tot_le n sender
                → ∀ (b_1 : Bool),
                  (b_1 = Bool.true) = (sender = n)
                    → ∀ (L1_1 L2_1 : node),
                      (if b_1 = Bool.true then
                         ¬ n = L1_1 → st_leader L1_1 = Bool.true
                       else
                         st_leader L1_1 = Bool.true)
                        → (if b_1 = Bool.true then
                             ¬ n = L2_1 → st_leader L2_1 = Bool.true
                           else
                             st_leader L2_1 = Bool.true)
                        → L1_1 = L2_1 := by
  epr (cegarRounds := 1000)
