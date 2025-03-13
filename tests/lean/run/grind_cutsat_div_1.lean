set_option grind.warning false
set_option grind.debug true
set_option pp.structureInstances false
open Int.Linear

theorem ex₁ (a : Int) (h₁ : 2 ∣ a) (h₂ : 2 ∣ 2*a + 1 - a) : False := by
  grind

theorem ex₂ (a b : Int) (h₀ : 2 ∣ a + 1) (h₁ : 2 ∣ b + a) (h₂ : 2 ∣ b + 2*a) : False := by
  grind

theorem ex₃ (a b : Int) (_ : 2 ∣ a + 1) (h₁ : 3 ∣ a + 3*b + a) (h₂ : 2 ∣ 3*b + a + 3 - b) (h₃ : 3 ∣ 3 * b + 2 * a + 1) : False := by
  grind

theorem ex₄ (f : Int → Int) (a b : Int) (_ : 2 ∣ f (f a) + 1) (h₁ : 3 ∣ f (f a) + 3*b + f (f a)) (h₂ : 2 ∣ 3*b + f (f a) + 3 - b) (h₃ : 3 ∣ 3 * b + 2 * f (f a) + 1) : False := by
  grind

#print ex₁
#print ex₂
#print ex₃
#print ex₄

/--
info: [grind.cutsat.assign] a := 1
[grind.cutsat.assign] b := 0
-/
#guard_msgs (info) in -- finds the model without any backtracking
set_option trace.grind.cutsat.assign true in
set_option trace.grind.cutsat.conflict true in
example (a b : Int) (_ : 2 ∣ a + 3) (_ : 3 ∣ a + b - 4) : False := by
  fail_if_success grind
  sorry

/--
info: [grind.cutsat.dvd] 2 ∣ a + 3
[grind.cutsat.dvd.update] 2 ∣ a + 3
[grind.cutsat.dvd] 3 ∣ a + 3*b + -4
[grind.cutsat.dvd.update] 3 ∣ 3*b + a + -4
[grind.cutsat.assign] a := 1
[grind.cutsat.assign] b := 0
-/
#guard_msgs (info) in
set_option trace.grind.cutsat.assign true in
set_option trace.grind.cutsat.dvd true in
set_option trace.grind.cutsat.dvd.solve.elim false in
set_option trace.grind.cutsat.dvd.solve.combine false in
set_option trace.grind.cutsat.dvd.trivial false in
set_option trace.grind.cutsat.conflict true in
example (a b : Int) (_ : 2 ∣ a + 3) (_ : 3 ∣ a + 3*b - 4) : False := by
  fail_if_success grind
  sorry

/--
info: [grind.cutsat.assign] a := 1
[grind.cutsat.assign] b := 15
-/
#guard_msgs (info) in
set_option trace.grind.cutsat.assign true in
set_option trace.grind.cutsat.conflict true in
example (a b : Int) (_ : 2 ∣ a + 3) (_ : 3 ∣ a + b - 4) (_ : b < 18): False := by
  fail_if_success grind
  sorry

/--
info: [grind.cutsat.assign] a := 1
[grind.cutsat.assign] b := 12
-/
#guard_msgs (info) in
set_option trace.grind.cutsat.assign true in
set_option trace.grind.cutsat.conflict true in
example (a b : Int) (_ : 2 ∣ a + 3) (_ : 3 ∣ a + b - 4) (_ : b ≥ 11): False := by
  fail_if_success grind
  sorry

/--
info: [grind.cutsat.assign] 「f 0」 := 11
[grind.cutsat.assign] 「f 1」 := 2
-/
#guard_msgs (info) in
set_option trace.grind.cutsat.assign true in
set_option trace.grind.cutsat.conflict true in
example (f : Int → Int) (_ : 2 ∣ f 0 + 3) (_ : 3 ∣ f 0 + f 1 - 4) (_ : f 0 ≥ 11): False := by
  fail_if_success grind
  sorry
