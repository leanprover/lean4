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

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval [1, 2, 3].iter.ensureTermination.toList

/-- info: [3, 2, 1] -/
#guard_msgs in
#eval [1, 2, 3].iter.toListRev

/-- info: [3, 2, 1] -/
#guard_msgs in
#eval [1, 2, 3].iter.ensureTermination.toListRev

/-- info: #[1, 2, 3] -/
#guard_msgs in
#eval [1, 2, 3].iter.toArray

/-- info: #[1, 2, 3] -/
#guard_msgs in
#eval [1, 2, 3].iter.ensureTermination.toArray

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

section Array

example : #[1, 2, 3].iter.toArray = #[1, 2, 3] := by
  simp

example : #[1, 2, 3].iter.toList = [1, 2, 3] := by
  simp

example : #[1, 2, 3].iter.toListRev = [3, 2, 1] := by
  simp

example : (#[1, 2, 3].iterFromIdx 2).toList = [3] := by
  simp

end Array

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
  simp [← Std.Iter.foldl_toList, List.sum]
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

def forInIO (l : List Nat) : IO Nat := do
  let mut s := 0
  for x in l.iter do
    IO.println s!"adding {x}"
    s := s + x
  return s

/--
info: adding 1
adding 2
---
info: 3
-/
#guard_msgs in
#eval forInIO [1, 2]

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

section Drop

def sumDropRec (l : List Nat) : Nat :=
  go (l.iter.drop 1) 0
where
  go it acc :=
    match it.step with
    | .yield it' out _ => go it' (acc + out)
    | .skip it' _ => go it' acc
    | .done _ => acc
  termination_by it.finitelyManySteps

def sumDropFold (l : List Nat) : Nat :=
  l.iter.drop 1 |>.fold (init := 0) (· + ·)

/-- info: [2, 3] -/
#guard_msgs in
#eval [1, 2, 3].iter.drop 1 |>.toList

/-- info: 5 -/
#guard_msgs in
#eval sumDropRec [1, 2, 3]

/-- info: 5 -/
#guard_msgs in
#eval sumDropFold [1, 2, 3]

example : ([1, 2, 3].iter.drop 1).toList = [2, 3] := by
  simp

example : ([1, 2, 3].iter.drop 1).toArray = #[2, 3] := by
  simp

example : ([1, 2, 3].iter.drop 1).toListRev = [3, 2] := by
  simp

end Drop

section FilterMap

example : ([1, 2, 3].iter.filterMap (fun x => if x % 2 = 0 then some (x / 2) else none)).toList =
    [1] := by
  simp

example : ([1, 2, 3].iter.map (· * 2)).toList = [2, 4, 6] := by
  simp

example : ([1, 2, 3].iter.filter (· % 2 = 0)).toList = [2] := by
  simp

example : ([1, 2, 3].iter.map (· * 2)).fold (init := 0) (· + ·) = 12 := by
  rw [Std.Iter.fold_map, ← Std.Iter.foldl_toList]
  simp

-- This test ensures that the `foldM_mapM` lemma is applicable without producing
-- monad-lifting diamonds. The test is so abstract because using three concrete monads and
-- liftings between them would make the test too complicated.
example {α : Type} {m n o : Type → Type} [Monad m] [Monad n] [Monad o]
    [LawfulMonad m] [LawfulMonad n] [LawfulMonad o]
    [MonadLift m n] [MonadLift n o] [LawfulMonadLift m n] [LawfulMonadLift n o]
    [Std.Iterator α m Nat] [Std.Iterators.Finite α m]
    [Std.IteratorLoop α m n] [Std.IteratorLoop α m o]
    [Std.IteratorLoop α m o]
    [Std.LawfulIteratorLoop α m n] [Std.LawfulIteratorLoop α m o]
    [Std.LawfulIteratorLoop α m o]
    [MonadAttach n] [WeaklyLawfulMonadAttach n]
    (it : Std.IterM (α := α) m Nat) (f : Nat → n Nat) (g : Nat → Nat → o Nat) :
    (it.mapM f).foldM g init = it.foldM (fun b a => do g b (← f a)) init := by
  rw [Std.IterM.foldM_mapM]

/--
info: Lean
is
fun
-/
#guard_msgs in
#eval ["Lean", "is", "fun"].iter.mapM (IO.println s!"{·}") |>.drain

-- This example demonstrates that chained `mapM` calls are executed in a different order than with `List.mapM`.
def chainedMapM (l : List Nat) : IO Unit :=
  l.iterM IO |>.mapM (IO.println <| s!"1st {.}") |>.mapM (IO.println <| s!"2nd {·}") |>.drain

/--
info: 1st 1
2nd ()
1st 2
2nd ()
1st 3
2nd ()
-/
#guard_msgs in
#eval! chainedMapM [1, 2, 3]

end FilterMap

section Zip

example : ([1, 2, 3].iter.zip ["one", "two"].iter).toList =
    [(1, "one"), (2, "two")] := by
  simp

example : ([1, 2, 3].iter.zip ["one", "two"].iter).toListRev =
    [(2, "two"), (1, "one")] := by
  simp

example : ([1, 2, 3].iter.zip ["one", "two"].iter).toArray =
    #[(1, "one"), (2, "two")] := by
  simp

end Zip

section TakeWhile

example : ([1, 2, 3, 4].iter.takeWhile (· ≠ 3)).toList = [1, 2] := by
  simp

example : ([1, 2, 3, 4].iter.takeWhile (· ≠ 3)).toArray = #[1, 2] := by
  simp

example : ([1, 2, 3, 4].iter.takeWhile (· ≠ 3)).toListRev = [2, 1] := by
  simp

end TakeWhile

section DropWhile

example : ([1, 2, 3, 4].iter.dropWhile (· ≠ 3)).toList = [3, 4] := by
  simp

example : ([1, 2, 3, 4].iter.dropWhile (· ≠ 3)).toArray = #[3, 4] := by
  simp

example : ([1, 2, 3, 4].iter.dropWhile (· ≠ 3)).toListRev = [4, 3] := by
  simp

end DropWhile

section Repeat

@[simp]
def positives := Std.Iter.repeat (init := 1) (· + 1)

example : (positives.take 5).toList = [1, 2, 3, 4, 5] := by
  simp

@[simp]
def divisors (n : Nat) := (positives.take n |>.filter (n % · = 0))

@[simp]
def isPrime (n : Nat) : Bool := (divisors n).toList.length == 2

example : isPrime 5 := by
  simp

end Repeat

section Empty

/-- info: [] -/
#guard_msgs in
#eval (Std.Iter.empty Nat).toList

example : (Std.Iter.empty Nat).toList = [] := by
  simp

end Empty

section Termination

example := positives.toList
example := positives.toListRev
example := positives.toArray

/--
error: failed to synthesize instance of type class
  Std.Iterators.Finite (Std.Iterators.Types.RepeatIterator Nat fun x => x + 1) Id

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example := positives.ensureTermination.toList

/--
error: failed to synthesize instance of type class
  Std.Iterators.Finite (Std.Iterators.Types.RepeatIterator Nat fun x => x + 1) Id

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example := positives.ensureTermination.toListRev

/--
error: failed to synthesize instance of type class
  Std.Iterators.Finite (Std.Iterators.Types.RepeatIterator Nat fun x => x + 1) Id

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example := positives.ensureTermination.toArray

end Termination
