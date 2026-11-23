import Std.Tactic.BVDecide

set_option trustCompiler true
/-
source: Examples/Ivy/ChordRingMaintenance.lean
vc: inherit_manual_6
epr: true
epr_info: EPR (stratified); sort edges: none
non_core_constants: none
standalone_check: ok
-/

open Classical in
theorem inherit_manual_6
    : ∀ (node : Type) (x y z th_org th_other : node) (st_a : node → Bool)
        (st_s1 : node → node → Bool) (st_in_s1 : node → Bool) (st_s2 : node → node → Bool)
        (st_in_s2 : node → Bool) (st_p : node → node → Bool) (st_reach st_error : node → Bool),
      th_other ≠ th_org
        → ∀ (ring_btw : node → node → node → Prop),
          (∀ (w x_1 y_1 z_1 : node), ring_btw w x_1 y_1 → ring_btw w y_1 z_1 → ring_btw w x_1 z_1)
            → (∀ (w_1 x_2 y_2 : node), ring_btw w_1 x_2 y_2 → ¬ ring_btw w_1 y_2 x_2)
            → (∀ (w_2 x_3 y_3 : node),
              ring_btw w_2 x_3 y_3 ∨ ring_btw w_2 y_3 x_3 ∨ w_2 = x_3 ∨ x_3 = y_3)
            → (∀ (x_4 y_4 z_2 : node), ring_btw x_4 y_4 z_2 ∧ x_4 ≠ z_2 → ring_btw y_4 z_2 x_4)
            → (∀ (N : node), ¬ st_error N = Bool.true)
            → (∀ (X Y : node), st_s1 X Y = Bool.true → st_in_s1 X = Bool.true)
            → (∀ (X_1 Y_1 : node), st_s2 X_1 Y_1 = Bool.true → st_in_s2 X_1 = Bool.true)
            → st_reach th_org = Bool.true
            → (∀ (X_2 Y_2 Z : node), st_s1 X_2 Y_2 = Bool.true ∧ st_s1 X_2 Z = Bool.true → Y_2 = Z)
            → (∀ (X_3 Y_3 Z_1 : node),
              st_s2 X_3 Y_3 = Bool.true ∧ st_s2 X_3 Z_1 = Bool.true → Y_3 = Z_1)
            → (∀ (X_4 Y_4 Z_2 : node),
              st_p X_4 Y_4 = Bool.true ∧ st_p X_4 Z_2 = Bool.true → Y_4 = Z_2)
            → (∀ (X_5 : node), st_a X_5 = Bool.true ∨ X_5 ≠ th_org)
            → (∀ (X_6 Y_5 : node),
              st_a X_6 = Bool.true ∨ ¬ st_p Y_5 X_6 = Bool.true ∨ ¬ st_s1 X_6 Y_5 = Bool.true)
            → (∀ (X_7 Y_6 : node),
              st_a X_7 = Bool.true ∨ st_p Y_6 X_7 = Bool.true ∨ ¬ st_s1 X_7 Y_6 = Bool.true)
            → (∀ (X_8 Y_7 : node), st_a X_8 = Bool.true ∨ ¬ st_s2 X_8 Y_7 = Bool.true)
            → (∀ (X_9 : node), st_in_s1 X_9 = Bool.true ∨ ¬ st_a X_9 = Bool.true)
            → (∀ (Y_8 Z_3 X_10 : node),
              st_a Y_8 = Bool.true ∨ st_a Z_3 = Bool.true ∨ ¬ st_s1 X_10 Y_8 = Bool.true
                ∨ ¬ st_s2 X_10 Z_3 = Bool.true)
            → (∀ (Y_9 X_11 : node),
              st_a Y_9 = Bool.true ∨ st_in_s2 X_11 = Bool.true ∨ ¬ st_a X_11 = Bool.true
                ∨ ¬ st_s1 X_11 Y_9 = Bool.true)
            → (∀ (A B : node), st_p A B = Bool.true → st_a A = Bool.true)
            → (∀ (X_12 Y_10 : node),
              st_a X_12 = Bool.true ∧ st_p Y_10 X_12 = Bool.true ∧ st_s1 X_12 Y_10 = Bool.true
                → st_a Y_10 = Bool.true)
            → (∀ (X_13 Y_11 : node), ¬ ring_btw X_13 th_org Y_11 ∨ ¬ st_s1 X_13 Y_11 = Bool.true)
            → (∀ (V0 V1 V2 : node),
              ¬(st_s1 V0 V1 = Bool.true ∧ V1 ≠ th_org ∧ st_s2 V0 V2 = Bool.true
                ∧ ring_btw V0 th_org V2))
            → st_a x = Bool.true → st_s1 x y = Bool.true → st_a y = Bool.true
            → st_s1 y z = Bool.true
            → ∀ (X_14 Y_12 Z_4 : node),
              st_p X_14 Y_12 = Bool.true → st_p X_14 Z_4 = Bool.true → Y_12 = Z_4 := by
  epr (cegarRounds := 1000)
