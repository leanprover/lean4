-- This validates that Lean is able to simplify patterns containing operations
-- on ground natural literals.
--
-- This is a regression test for #3139.
set_option maxHeartbeats 1000

-- This fails without the fix and maxHeartbeats 1000.
def testZeroAdd (x:Nat) :=
  match x with
  | 0 + 128 => true
  | _ => false

-- This succeeds in all cases
def testAddZero (x:Nat) :=
  match x with
  | 128 + 0 => true
  | _ => false
