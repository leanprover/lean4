/-!
Tests well-founded recursion over `String.Pos` whose termination proof is discharged by
`decreasing_tactic`, using the hypothesis of an `if h : ...` or a `match h : ...`, and that the
resulting functions can be evaluated and compiled.
-/

def numChars (s : String) : Nat :=
  go s.startPos
where
  go (p : s.Pos) : Nat :=
    if h : p ≠ s.endPos then
      go (p.next h) + 1
    else
      0
  termination_by p

#guard numChars "aαc" == 3

example : numChars "aαc" = 3 := by native_decide

def numChars2 (s : String) : Nat :=
  go s.startPos
where
  go (p : s.Pos) : Nat :=
    match h : p.next? with
    | some q => go q + 1
    | none   => 0
  termination_by p

example : numChars2 "aαc" = 3 := by native_decide
