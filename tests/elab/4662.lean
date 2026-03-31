/--
error: `<identifier>@<term>` is a named pattern and can only be used in pattern matching contexts
  p@()
-/
#guard_msgs in
def minimal : Unit -> Unit := by
  intro i
  let k:p@() := i
  sorry

def minimal2 : Unit -> Unit := by
  intro i
  let p@k:() := i
  guard_hyp k : p = ()
  exact ()
