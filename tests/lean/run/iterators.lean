import Std.Data.Iterators

section ListIteratorBasic

/-- info: [1, 2, 3].iter : Std.Iter Nat -/
#guard_msgs in
#check [1, 2, 3].iter

/-- info: [1, 2, 3].iterM Id : Std.IterM Id Nat -/
#guard_msgs in
#check [1, 2, 3].iterM Id

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval [1, 2, 3].iter.toList

/-- info: #[1, 2, 3] -/
#guard_msgs in
#eval [1, 2, 3].iter.toArray

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval [1, 2, 3].iter |>.allowNontermination.toList

/-- info: ([1, 2, 3].iterM IO).toList : IO (List Nat) -/
#guard_msgs in
#check [1, 2, 3].iterM IO |>.toList

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval [1, 2, 3].iterM IO |>.toList

/-- info: #[1, 2, 3] -/
#guard_msgs in
#eval [1, 2, 3].iterM IO |>.toArray

example : [1, 2, 3].iter.toList = [1, 2, 3] := by
  simp

example : [1, 2, 3].iter.toArray = #[1, 2, 3] := by
  simp

example : [1, 2, 3].iter.toListRev = [3, 2, 1] := by
  simp

-- This does not work for `IO` because `LawfulMonad IO` is in Batteries
example : ([1, 2, 3].iterM (StateM Nat)).toList = pure [1, 2, 3] := by
  simp

example : ([1, 2, 3].iterM (StateM Nat)).toArray = pure #[1, 2, 3] := by
  simp

example : ([1, 2, 3].iterM (StateM Nat)).toListRev = pure [3, 2, 1] := by
  simp

end ListIteratorBasic

section WellFoundedRecursion

def sum (l : List Nat) : Nat :=
  go l.iter 0
where
  go it acc :=
    match it.step with
    | .yield it' out _ => go it' (acc + out)
    | .skip it' _ => go it' acc
    | .done _ => acc
  termination_by it.finitelyManySteps

/-- info: 6 -/
#guard_msgs in
#eval sum [1, 2, 3]

end WellFoundedRecursion

section Loop

def sumFold (l : List Nat) : Nat :=
  l.iter.fold (init := 0) (· + ·)

/-- info: 6 -/
#guard_msgs in
#eval [1, 2, 3].iter.fold (init := 0) (· + · )

example (l : List Nat) : l.iter.fold (init := 0) (· + ·) = l.sum := by
  simp [← Std.Iterators.Iter.foldl_toList, List.sum]
  -- It remains to show that List.foldl (· + ·) = List.foldr (· + ·)
  generalize 0 = init
  induction l generalizing init
  · rfl
  · rename_i x l ih
    simp only [List.foldl_cons, ih, List.foldr_cons]
    clear ih
    induction l generalizing x
    · simp only [List.foldr_nil]
      omega
    · simp only [List.foldr_cons, *]
      omega

example (l : List Nat) :
  (Id.run do
    let mut s := 0
    for x in l.iter do
      s := s + x
    return s) = l.iter.fold (init := 0) (· + ·) := by
  simp

end Loop

section Take

def sumTakeRec (l : List Nat) : Nat :=
  go (l.iter.take 2) 0
where
  go it acc :=
    match it.step with
    | .yield it' out _ => go it' (acc + out)
    | .skip it' _ => go it' acc
    | .done _ => acc
  termination_by it.finitelyManySteps

def sumTakeFold (l : List Nat) : Nat :=
  l.iter.take 2 |>.fold (init := 0) (· + ·)

/-- info: [1, 2] -/
#guard_msgs in
#eval [1, 2, 3].iter.take 2 |>.toList

/-- info: 3 -/
#guard_msgs in
#eval sumTakeRec [1, 2, 3]

/-- info: 3 -/
#guard_msgs in
#eval sumTakeFold [1, 2, 3]

example : ([1, 2, 3].iter.take 2).toList = [1, 2] := by
  simp

example : ([1, 2, 3].iter.take 2).toArray = #[1, 2] := by
  simp

example : ([1, 2, 3].iter.take 2).toListRev = [2, 1] := by
  simp

end Take
