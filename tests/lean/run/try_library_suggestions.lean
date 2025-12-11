import Lean.LibrarySuggestions

-- Test that try? can find solutions using grind? +suggestions

-- Test 1: Regular tactics should be tried first (rfl should win)
/--
info: Try these:
  [apply] rfl
  [apply] simp
  [apply] simp only
  [apply] grind
  [apply] grind only
  [apply] simp_all
-/
#guard_msgs in
example : 5 = 5 := by
  try?

-- Test 2: A theorem that requires library suggestions
-- Define an opaque constant so grind can't unfold it
axiom SpecialProperty : Nat → Prop

-- A specific instance that's provable
axiom special_7 : SpecialProperty 7

-- Set up a premise selector that suggests special_7
set_library_suggestions (fun _ _ => pure #[{ name := `special_7, score := 1.0 }])

-- Expected: try? should find grind only [special_7]
/--
info: Try these:
  [apply] grind only [special_7]
  [apply] grind => instantiate only [special_7]
-/
#guard_msgs in
example : SpecialProperty 7 := by
  try?

-- Test 3: For simp_all testing, use an axiom-based approach
axiom CustomOp : Nat → Nat → Nat

-- A property about CustomOp that can't be proven by unfolding
axiom custom_comm : ∀ x y, CustomOp x y = CustomOp y x

-- Set up a premise selector that suggests custom_comm
set_library_suggestions (fun _ _ => pure #[{ name := `custom_comm, score := 1.0 }])

-- Expected: try? should find grind only [custom_comm]
/--
info: Try these:
  [apply] grind only [custom_comm]
  [apply] grind => instantiate only [custom_comm]
-/
#guard_msgs in
example (a b : Nat) : CustomOp a b = CustomOp b a := by
  try?

-- Test 4: With a hypothesis that needs library suggestions
/--
info: Try these:
  [apply] grind only [custom_comm]
  [apply] grind => instantiate only [custom_comm]
-/
#guard_msgs in
example (a b c : Nat) (h : CustomOp a b = c) : CustomOp b a = c := by
  try?

-- Test 5: Multiple library suggestions with grind
axiom Property1 : Nat → Prop
axiom Property2 : Nat → Prop

axiom prop1_5 : Property1 5
axiom prop2_5 : Property2 5

-- Set up a premise selector with multiple suggestions
set_library_suggestions (fun _ _ => pure #[
  { name := `prop1_5, score := 0.9 },
  { name := `prop2_5, score := 0.7 }
])

-- Expected: try? should use the best applicable one
/--
info: Try these:
  [apply] grind only [prop1_5]
  [apply] grind => instantiate only [prop1_5]
-/
#guard_msgs in
example : Property1 5 := by
  try?
