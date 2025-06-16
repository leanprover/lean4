
-- Check that indent is required

def nullary1 (x : Nat) : Option Unit := nullary1 (x + 1)
partial_fixpoint monotonicity
fun _ _ a x => a (x + 1)

def nullary2 (x : Nat) : Option Unit := nullary2 (x + 1)
partial_fixpoint
monotonicity fun _ _ a x => a (x + 1)

-- This is allowed:

def nullary3 (x : Nat) : Option Unit := nullary3 (x + 1)
partial_fixpoint
    monotonicity
  fun _ _ a x => a (x + 1)
