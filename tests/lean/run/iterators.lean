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

end ListIteratorBasic

section WellFoundedRecursion

def sum (l : List Nat) : Nat :=
  go l.iter 0
where
  @[specialize] -- The old code generator seems to need this.
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

end Loop

section Take

def sumTakeRec (l : List Nat) : Nat :=
  go (l.iter.take 2) 0
where
  @[specialize] -- The old code generator seems to need this.
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

end Take
