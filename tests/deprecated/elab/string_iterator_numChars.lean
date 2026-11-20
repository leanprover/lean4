/-!
Tests well-founded recursion over the deprecated `String.Iterator`, whose termination proof is
inferred and discharged by `decreasing_tactic` using the hypothesis of an `if h : ...` or a
`match h : ...`. The `String.Pos` version is `elab/numChars.lean`.
-/

def numChars (s : String) : Nat :=
  go s.iter
where
  go (i : String.Legacy.Iterator) : Nat :=
    if h : i.hasNext then
      go i.next + 1
    else
      0

#guard numChars "aαc" == 3

example : numChars "aαc" = 3 := by native_decide

def numChars2 (s : String) : Nat :=
  go s.iter
where
  go (i : String.Legacy.Iterator) : Nat :=
    match h : i.hasNext with
    | true  => go i.next + 1
    | false => 0

example : numChars2 "aαc" = 3 := by native_decide
