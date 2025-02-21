set_option grind.warning false
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
info: [grind.cutsat.assign] a := -3
[grind.cutsat.assign] b := 7
-/
#guard_msgs (info) in -- finds the model without any backtracking
set_option trace.grind.cutsat.assign true in
set_option trace.grind.cutsat.conflict true in
example (a b : Int) (_ : 2 ∣ a + 3) (_ : 3 ∣ a + b - 4) : False := by
  fail_if_success grind
  sorry


/--
info: [grind.cutsat.dvd.update] 2 ∣ a + 3
[grind.cutsat.dvd.update] 3 ∣ 3 * b + a + -4
[grind.cutsat.assign] a := -3
[grind.cutsat.conflict] 3 ∣ 3 * b + a + -4
[grind.cutsat.dvd.solve] 3 ∣ a + -4, 2 ∣ a + 3
[grind.cutsat.dvd.update] 6 ∣ a + 17
[grind.cutsat.assign] a := -17
[grind.cutsat.assign] b := 0
-/
#guard_msgs (info) in
set_option trace.grind.cutsat.assign true in
set_option trace.grind.cutsat.dvd true in
set_option trace.grind.cutsat.dvd.solve.elim false in
set_option trace.grind.cutsat.dvd.solve.combine false in
set_option trace.grind.cutsat.dvd.trivial false in
set_option trace.grind.cutsat.conflict true in
/-
In this example, cutsat fails to extend the model to `b` after assigning `a := - 3`.
Then, it learns a new constraaint `6 ∣ a + 17`, finds a new assignment for `a := -17`
and then satisfies `3 ∣ a + 3*b - 4`, but assigning `b := 0`.
So model (aka counter-example) is `a := -17` and `b := 0`.
-/
example (a b : Int) (_ : 2 ∣ a + 3) (_ : 3 ∣ a + 3*b - 4) : False := by
  fail_if_success grind
  sorry
