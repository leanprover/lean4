import Std.Data.HashMap
import Std.Data.Iterators
import Std.Data.HashSet
import Std.Data.HashSet.Iterator

/-!
Benchmark for the built-in `Std.Data.HashMap`, inspired by:
- https://github.com/google/hashtable-benchmarks
- https://github.com/rust-lang/hashbrown/blob/master/benches/bench.rs

all times reported are average times for the operation described in the name of the benchmark
in nanoseconds.
-/

set_option compiler.extract_closed false

structure RandomIterator where
  state : UInt64

@[inline]
def iterRandM (seed : UInt64) : Std.IterM (α := RandomIterator) m UInt64 :=
  { internalState := RandomIterator.mk seed }

@[inline]
def iterRand (seed : UInt64) : Std.Iter (α := RandomIterator) UInt64 :=
  { internalState := RandomIterator.mk seed }

instance [Pure m] : Std.Iterator RandomIterator m UInt64 where
  IsPlausibleStep it
    | .yield it' out => True -- fake it for now
    | .skip _ => False
    | .done => False
  step := fun ⟨it⟩ =>
    pure (.deflate ⟨.yield (iterRandM <| (it.state + (1 : UInt64)) * (3_787_392_781 : UInt64)) it.state, by trivial⟩)

def mkMapWithCap (seed : UInt64) (size : Nat) : Std.HashMap UInt64 UInt64 := Id.run do
  let mut map := Std.HashMap.emptyWithCapacity size
  for val in iterRand seed |>.take size |>.allowNontermination do
    map := map.insert val val
  return map

def timeNanos (reps : Nat) (x : IO Unit) : IO Float := do
  let startTime ← IO.monoNanosNow
  x
  let endTime ← IO.monoNanosNow
  return (endTime - startTime).toFloat / reps.toFloat

def REP : Nat := 100

/-
Return the average time it takes to check that a hashmap `contains` an element that is contained.
-/
def benchContainsHit (seed : UInt64) (size : Nat) : IO Float := do
  let map := mkMapWithCap seed size
  let checks := size * REP
  timeNanos checks do
    let mut todo := checks
    while todo != 0 do
      for val in iterRand seed |>.take size |>.allowNontermination do
        if !map.contains val then
          throw <| .userError "Fail"
      todo := todo - size

/-
Return the average time it takes to check that a hashmap `contains` an element that is not contained.
-/
def benchContainsMiss (seed : UInt64) (size : Nat) : IO Float := do
  let map := mkMapWithCap seed size
  let checks := size * REP
  let iter := iterRand seed |>.drop size
  timeNanos checks do
    let mut todo := checks
    while todo != 0 do
      for val in iter |>.take size |>.allowNontermination do
        if map.contains val then
          throw <| .userError "Fail"
      todo := todo - size

/-
Return the average time it takes to read an element from a hashmap during iteration.
-/
def benchIterate (seed : UInt64) (size : Nat) : IO Float := do
  let map := mkMapWithCap seed size
  let checks := size * REP
  timeNanos checks do
    let mut todo := checks
    let mut sum := 0
    while todo != 0 do
      for (elem, _) in map do
        sum := sum + elem
        if sum == 0 then
          throw <| .userError "Fail"
      todo := todo - size

/-
Return the average time it takes to `insertIfNew` an element that is contained in the hashmap.
This value should be close to `benchContainsHit`
-/
def benchInsertIfNewHit (seed : UInt64) (size : Nat) : IO Float := do
  let map := mkMapWithCap seed size
  let checks := size * REP
  timeNanos checks do
    let mut todo := checks
    let mut map := map
    while todo != 0 do
      for val in iterRand seed |>.take size |>.allowNontermination do
        map := map.insertIfNew val val
        if map.size != size then
          throw <| .userError "Fail"
      todo := todo - size

/-
Return the average time it takes to unconditionally `insert` (or rather, update) an element that is
contained in the hashmap.
-/
def benchInsertHit (seed : UInt64) (size : Nat) : IO Float := do
  let map := mkMapWithCap seed size
  let checks := size * REP
  timeNanos checks do
    let mut todo := checks
    let mut map := map
    while todo != 0 do
      for val in iterRand seed |>.take size |>.allowNontermination do
        map := map.insert val val
        if map.size != size then
          throw <| .userError "Fail"
      todo := todo - size

/--
Return the average time it takes to `insert` a new element into a hashmap that might resize.
-/
def benchInsertMissEmpty (seed : UInt64) (size : Nat) : IO Float := do
  let checks := size * REP
  timeNanos checks do
    let mut todo := checks
    while todo != 0 do
      let mut map : Std.HashMap _ _ := {}
      for val in iterRand seed |>.take size |>.allowNontermination do
        map := map.insert val val
        if map.size > size then
          throw <| .userError "Fail"
      todo := todo - size

/--
Return the average time it takes to `insert` a new element into a hashmap that will not resize.
-/
def benchInsertMissEmptyWithCapacity (seed : UInt64) (size : Nat) : IO Float := do
  let checks := size * REP
  timeNanos checks do
    let mut todo := checks
    while todo != 0 do
      let mut map := Std.HashMap.emptyWithCapacity size
      for val in iterRand seed |>.take size |>.allowNontermination do
        map := map.insert val val
        if map.size > size then
          throw <| .userError "Fail"
      todo := todo - size

/--
Return the average time it takes to `erase` an existing and `insert` a new element into a hashmap.
-/
def benchEraseInsert (seed : UInt64) (size : Nat) : IO Float := do
  let map := mkMapWithCap seed size
  let checks := size * REP
  let eraseIter := iterRand seed
  let newIter := iterRand seed |>.drop size
  timeNanos checks do
    let mut map := map
    let mut todo := checks
    while todo != 0 do
      for (eraseVal, newVal) in eraseIter.zip newIter |>.take size |>.allowNontermination do
        map := map.erase eraseVal |>.insert newVal newVal
        if map.size != size then
          throw <| .userError "Fail"
      todo := todo - size

section anyTests

def testPrimes : List Nat := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71]

def List.getfirst (l : List α) (n : Nat) :=
  match n with
  | .zero => List.nil
  | .succ m =>
    match l with
    | .nil => nil
    | .cons hd tl => hd::(tl.getfirst m)

def createTest : IO (Std.HashSet Nat ) := do
  let mut set := Std.HashSet.emptyWithCapacity (α := Nat) 100
  let mut i:= 0

  while i < 100 do
    set := set.insert i
    i := (i + 1)

  return set

set_option trace.compiler.ir true in
def test : IO Unit := do
  let set ← createTest

  let res := set.iter.any (fun x => [2,3,5].all (fun y => x%y = 0))

  if (res || ! res) = false then
    throw <| .userError "Fail"

/--
  Returns the average time to find solutions to a chinese remainder problem using the built-in any function of the hashset
-/
def benchNativeAny (size : Nat) : IO Float := do
    let mut set := Std.HashSet.emptyWithCapacity (α := Nat) size
    let checks := size * REP
    let mut i := 1

    while i < size do
      set := set.insert i
      i := (i + 1)

    timeNanos checks do
      let mut j:= 0

      while j < testPrimes.length do
        let res := set.any (fun x => (testPrimes.getfirst j).all (fun y => x % y = 0))
        if (res || !res) = false then
          throw <| .userError "Fail"
        j := j + 1

/--
  Returns the average time to find solutions to a chinese remainder problem by converting it first to an iterator and using the iterators any function
-/
def benchIterAny (size : Nat) : IO Float := do
    let mut set := Std.HashSet.emptyWithCapacity (α := Nat) size
    let checks := size * REP
    let mut i := 1

    while i < size do
      set := set.insert i
      i := (i + 1)

    timeNanos checks do
      let mut j:= 0

      while j < testPrimes.length do
        let res := set.iter.any (fun x => (testPrimes.getfirst j).all (fun y => x % y = 0))
        if (res || !res) = false then
          throw <| .userError "Fail"
        j := j + 1

def compareAnyBench : IO Unit := do
  let inputSizes := [100, 500, 1000, 5000, 10000, 100000]
  let mut nativeBetter := 0
  let mut iteratorBetter := 0

  for size in inputSizes do
    if (← benchNativeAny size) < (← benchIterAny size)
    then nativeBetter := nativeBetter + 1
    else iteratorBetter := iteratorBetter + 1

  IO.println s!"Native function better: {nativeBetter}"
  IO.println s!"Iterator function better: {iteratorBetter}"

#eval compareAnyBench

end anyTests

def main (args : List String) : IO Unit := do
  let seed := args[0]!.toNat!.toUInt64
  let size := args[1]!.toNat!
  assert! size % REP == 0
  let benches := [
    ("containsHit", benchContainsHit),
    ("containsMiss", benchContainsMiss),
    ("iterate", benchIterate),
    ("insertIfNewHit", benchInsertIfNewHit),
    ("insertHit", benchInsertHit),
    ("insertMissEmpty", benchInsertMissEmpty),
    ("insertMissEmptyWithCapacity", benchInsertMissEmptyWithCapacity),
    ("eraseInsert", benchEraseInsert),
  ]

  for (name, benchFunc) in benches do
    let time ← benchFunc seed size
    IO.println s!"{name}: {time}"
