/-!
# Sorry Warning Declaration Name Test

Tests that sorry warnings include the declaration name.
-/

-- Test: Warning includes declaration name
/--
warning: declaration `mySorryDef` uses `sorry`
-/
#guard_msgs in
def mySorryDef : Nat := sorry

-- Test: Theorem name shown
/--
warning: declaration `mySorryThm` uses `sorry`
-/
#guard_msgs in
theorem mySorryThm : True := sorry

-- Test: Recursive definition
/--
warning: declaration `recDef` uses `sorry`
-/
#guard_msgs in
def recDef : Nat → Nat
  | 0 => 0
  | n + 1 => sorry

-- Test: Mutual recursion (non-recursive bodies to avoid internal defs)
/--
warning: declaration `mutualB` uses `sorry`
---
warning: declaration `mutualA` uses `sorry`
-/
#guard_msgs in
mutual
def mutualA : Nat := mutualB + sorry
def mutualB : Nat := sorry
end

-- Test: Where clause
/--
warning: declaration `withWhere.helper` uses `sorry`
-/
#guard_msgs in
def withWhere : Nat := helper
where
  helper : Nat := sorry
