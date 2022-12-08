theorem le_of_not_lt {a b : Nat} (_: ¬ a < b): b ≤ a := sorry
theorem lt_of_succ_lt          (_: a + 1 < b): a < b := sorry
theorem succ_pred_eq_of_pos        (_: 0 < v): v - 1 + 1 = v := sorry

set_option trace.Meta.Tactic.simp true
--set_option trace.Debug.Meta.Tactic.simp true


example (h₁: k ≤ v - 1) (h₂: 0 < v):
    (if k ≤ v - 1 then Fin.mk (v-1+1) sorry else Fin.mk (v-1) sorry) = Fin.mk v sorry (n:=n) := by
    simp only [
      h₁, h₂,
      ite_true,
      succ_pred_eq_of_pos
      ----------------
      , le_of_not_lt
      , lt_of_succ_lt
    ]

-- it works

example (h₁: k ≤ v - 1) (h₂: 0 < v):
    (if k ≤ v - 1 then Fin.mk (v-1+1) sorry else Fin.mk (v-1) sorry) = Fin.mk v sorry (n:=n) := by
    simp (config := { memoize := false}) only [
      h₁, h₂,
      ite_true,
      succ_pred_eq_of_pos
      ----------------
      , le_of_not_lt
      , lt_of_succ_lt
    ]

example (h₁: k ≤ v - 1) (h₂: 0 < v):
    (if k ≤ v - 1 then Fin.mk (v-1+1) sorry else Fin.mk (v-1) sorry) = Fin.mk v sorry (n:=n) := by
    simp only [
      h₁, h₂,
      ite_true,
      succ_pred_eq_of_pos
      ----------------
      --, le_of_not_lt
      --, lt_of_succ_lt
    ]
