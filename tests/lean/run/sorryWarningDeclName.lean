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

-- Test: Partial definition (sorry is in _unsafe_rec, name should be stripped)
/--
warning: declaration `partialDef` uses `sorry`
-/
#guard_msgs in
partial def partialDef (n : Nat) : Nat :=
  if n == 0 then sorry else partialDef (n - 1)

-- Test: Let rec
/--
warning: declaration `withLetRec.helper` uses `sorry`
-/
#guard_msgs in
def withLetRec : Nat :=
  let rec helper : Nat → Nat
    | 0 => 0
    | n + 1 => sorry
  helper 5

-- Test: Multiple SCCs in mutual recursion
-- groupA depends on groupB (separate SCC from groupC)
-- groupC is independent SCC
/--
warning: declaration `groupC` uses `sorry`
---
warning: declaration `groupA` uses `sorry`
-/
#guard_msgs in
mutual
def groupA : Nat := groupB + sorry
def groupB : Nat := groupC + 1
def groupC : Nat := sorry
end

-- Test: Structural recursion with match
/--
warning: declaration `structRec` uses `sorry`
-/
#guard_msgs in
def structRec (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => sorry

-- Test: Recursive where
/--
warning: declaration `recWhere.loop` uses `sorry`
-/
#guard_msgs in
def recWhere (n : Nat) : Nat := loop n
where
  loop : Nat → Nat
    | 0 => 0
    | n + 1 => sorry
