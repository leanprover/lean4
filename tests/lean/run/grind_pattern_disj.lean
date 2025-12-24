/-
Tests for grind_pattern with disjunction support (CNF constraints)
-/

-- Test 1: Basic disjunction with not_value
axiom mod_eq_of_lt {a b : Nat} : a < b → a % b = a

grind_pattern mod_eq_of_lt => a % b where
  guard a < b
  not_value a or not_value b

-- Should succeed: symbolic a
example (h : a < 1024) : a % 1024 = a := by
  grind

-- Should succeed: symbolic b
example (h : 2 < b) : 2 % b = 2 := by
  grind

-- Test 2: Multiple constraints with disjunction
axiom array_extract_extract {as : Array α} {i j k l : Nat} :
  (as.extract i j).extract k l = as.extract (i + k) (min (i + l) j)

grind_pattern array_extract_extract => (as.extract i j).extract k l where
  not_value as or not_value i
  size as < 100

-- Should succeed: symbolic array
example {as : Array Nat} {i j k l : Nat} :
    (as.extract i j).extract k l = as.extract (i + k) (min (i + l) j) := by
  grind

-- Test 3: Three-way disjunction
axiom test_three_way {x y z : Nat} : x + y + z = z + y + x

grind_pattern test_three_way => x + y + z where
  not_value x or not_value y or not_value z

-- Should succeed: only one value is concrete
example : a + b + 5 = 5 + b + a := by
  grind

example : a + 3 + c = c + 3 + a := by
  grind

example : 2 + b + c = c + b + 2 := by
  grind

-- Test 4: Disjunction with other constraint types
axiom size_test {xs : List α} {ys : List α} : xs.length + ys.length = (xs ++ ys).length

grind_pattern size_test => xs.length + ys.length where
  size xs < 20 or size ys < 20

-- Should succeed: at least one list is small in size
example {xs ys : List Nat} : xs.length + ys.length = (xs ++ ys).length := by
  grind

-- Test 5: Error case - guard in disjunction should be rejected
/--
error: `guard` and `check` constraints cannot be used in disjunctions
-/
#guard_msgs in
grind_pattern mod_eq_of_lt => a % b where
  guard (a < b) or not_value a

-- Test 6: Error case - check in disjunction should be rejected
/--
error: `guard` and `check` constraints cannot be used in disjunctions
-/
#guard_msgs in
grind_pattern mod_eq_of_lt => a % b where
  check (a < b) or not_value a
