set_option grind.warning false
-- set_option grind.debug true -- TODO: enable after making more progress in `EqCnstr.lean`
open Int.Linear

-- set_option trace.grind.cutsat.assert true
-- set_option trace.grind.cutsat.internalize true

/-- info: [grind.cutsat.eq] b + 「f a」 + 1 = 0 -/
#guard_msgs (info) in
set_option trace.grind.cutsat.eq true in
example (a b : Int) (f : Int → Int) (h₁ : f a + b + 3 = 2)  : False := by
  fail_if_success grind
  sorry

theorem ex₁ (a b : Int) (_ : 2*a + 3*b = 0) (_ : 2 ∣ 3*b + 1) : False := by
  grind

theorem ex₂ (a b : Int) (_ : 2 ∣ 3*a + 1) (_ : 2*b + 3*a = 0) : False := by
  grind

set_option trace.grind.cutsat.subst true

theorem ex₃ (a b c : Int) (_ : c + 3*a = 0) (_ : 2 ∣ 3*a + 1) (_ : 2*b + c = 0) : False := by
  grind

theorem ex₄ (a b c : Int) (_ : 2*c + 3*a = 0) (_ : 2*b + c = 0) (_ : 2 ∣ 3*a + 1) : False := by
  grind

#print ex₁
#print ex₂
#print ex₃
#print ex₄
