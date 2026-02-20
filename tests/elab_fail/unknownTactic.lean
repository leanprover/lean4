theorem ex1 (x : Nat) : x = x → x = x := by
  intro
  aexact (rfl)

#print "---"

theorem ex2 (x : Nat) : x = x → x = x :=
  have : x = x := by foo
  fun h => h

#print "---"

theorem ex3 (x : Nat) : x = x → x = x :=
  have : x = x := by foo (aaa bbb)
  fun h => h
