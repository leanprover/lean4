import Std

set_option trace.Meta.Tactic.bv.epr true in
example {α : Type u} (a b : α) (h1 : a ≠ b) (h2 : ∀ (x y : α), x = y) {β : Type 1}
    (p : α → β → Prop) (c : β) (h : p a c): False := by
  bv_decide +epr

set_option trace.Meta.Tactic.bv.epr true in
theorem PaxosEPR.extracted_12707742549918667983086567387503966771 (node : Type) [node_dec : DecidableEq node]
  [node_ne : Nonempty node] (value : Type) [value_dec : DecidableEq value] [value_ne : Nonempty value] (quorum : Type)
  [quorum_dec : DecidableEq quorum] [quorum_ne : Nonempty quorum] (round : Type) [round_dec : DecidableEq round]
  [round_ne : Nonempty round] (tot_le : round → round → Prop) (tot_le_refl : ∀ (x : round), tot_le x x)
  (tot_le_trans : ∀ (x y z : round), tot_le x y → tot_le y z → tot_le x z)
  (tot_le_antisymm : ∀ (x y : round), tot_le x y → tot_le y x → x = y)
  (tot_le_total : ∀ (x y : round), tot_le x y ∨ tot_le y x) (st_none : round) (st_member : node → quorum → Prop)
  (st_one_a : round → Prop) (st_one_b_max_vote : node → round → round → value → Prop)
  (st_one_b st_left_rnd : node → round → Prop) (st_proposal : round → value → Prop)
  (st_vote st_decision : node → round → value → Prop)
  (st_1_none : round) (st_1_member : node → quorum → Prop) (st_1_one_a : round → Prop)
  (st_1_one_b_max_vote : node → round → round → value → Prop) (st_1_one_b st_1_left_rnd : node → round → Prop)
  (st_1_proposal : round → value → Prop) (st_1_vote st_1_decision : node → round → value → Prop)
  (a_1_1_left : st_none = st_1_none)
  (a_1_1_right_left : ∀ (a_1 : node) (a_2 : quorum), st_member a_1 a_2 = st_1_member a_1 a_2)
  (a_1_1_right_right_left : ∀ (a_1 : round), st_one_a a_1 = False)
  (a_1_1_right_right_right_left :
    ∀ (a_1 : node) (a_2 a_3 : round) (a_4 : value), st_one_b_max_vote a_1 a_2 a_3 a_4 = False)
  (a_1_1_right_right_right_right_left : ∀ (a_1 : node) (a_2 : round), st_one_b a_1 a_2 = False)
  (a_1_1_right_right_right_right_right_left : ∀ (a_1 : node) (a_2 : round), st_left_rnd a_1 a_2 = False)
  (a_1_1_right_right_right_right_right_right_left : ∀ (a_1 : round) (a_2 : value), st_proposal a_1 a_2 = False)
  (a_1_1_right_right_right_right_right_right_right_left :
    ∀ (a_1 : node) (a_2 : round) (a_3 : value), st_vote a_1 a_2 a_3 = False)
  (a_1_1_right_right_right_right_right_right_right_right :
    ∀ (a_1 : node) (a_2 : round) (a_3 : value), st_decision a_1 a_2 a_3 = False)
  (N1 : node) (R1 : round) (V1 : value) (N2 : node) (R2 : round) (V2 : value) :
  st_decision N1 R1 V1 →
    st_decision N2 R2 V2 →
      V1 =
        V2 := by grind




