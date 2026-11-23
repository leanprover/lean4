import Std.Tactic.BVDecide

set_option trustCompiler true
/-
source: Examples/Ivy/Ring.lean
vc: recv_single_leader
epr: true
epr_info: EPR (stratified); sort edges: none
non_core_constants: none
standalone_check: ok
-/

open Classical in
theorem recv_single_leader
    : ∀ (node : Type) (sender n next : node) (st_leader : node → Bool)
        (st_pending : node → node → Bool) [instNonempty : Nonempty node]
        (tot_le : node → node → Prop),
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
            → (∀ (N M : node), st_leader N = Bool.true ∧ st_leader M = Bool.true → N = M)
            → (∀ (L N_1 : node), st_leader L = Bool.true → tot_le N_1 L)
            → (∀ (L_1 N_2 : node), st_pending L_1 L_1 = Bool.true → tot_le N_2 L_1)
            → (∀ (S D N_3 : node), st_pending S D = Bool.true ∧ btwn_btw S N_3 D → tot_le N_3 S)
            → (∀ (Z : node), n ≠ next ∧ (Z ≠ n ∧ Z ≠ next → btwn_btw n next Z))
            → st_pending sender n = Bool.true
            → ∀ (b : Bool),
              (b = Bool.true) = tot_le n sender
                → ∀ (b_1 : Bool),
                  (b_1 = Bool.true) = (sender = n)
                    → ∀ (N_4 M_1 : node),
                      (if b_1 = Bool.true then
                         ¬ n = N_4 → st_leader N_4 = Bool.true
                       else
                         st_leader N_4 = Bool.true)
                        → (if b_1 = Bool.true then
                             ¬ n = M_1 → st_leader M_1 = Bool.true
                           else
                             st_leader M_1 = Bool.true)
                        → N_4 = M_1 := by
  epr (cegarRounds := 1000)
