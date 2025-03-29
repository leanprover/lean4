import Std.Tactic.BVDecide

-- This test exercises the AIG infrastructure, producing a giant AIG that needs to be serialized etc
example : ∀ (v6 v5 v1 v3 v2 v4 : BitVec 128),
    (v2.smtUDiv v3).smtUDiv ((v1.smtUDiv v2).smtUDiv (v1.smtUDiv v3)) != v6 * v4.smtUDiv v5  := by
  fail_if_success bv_decide
  sorry
