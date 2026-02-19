import Std

open List.MergeSort.Internal

@[noinline]
def sortListNat (xs : List Nat) : IO Nat := return (mergeSortTR₂ xs).length
@[noinline]
def sortArrayNat (xs : Array Nat) : IO Nat := return xs.mergeSort.size

@[noinline]
def sortListUInt64 (xs : List UInt64) : IO Nat := return (mergeSortTR₂ xs).length
@[noinline]
def sortArrayUInt64 (xs : Array UInt64) : IO Nat := return xs.mergeSort.size

def bench (label : String) (f g : IO Nat) : IO Unit := do
  let start ← IO.monoMsNow
  let r1 ← f
  let mid ← IO.monoMsNow
  let r2 ← g
  let done ← IO.monoMsNow
  let listMs := mid - start
  let arrayMs := done - mid
  let ratio := if listMs == 0 then 0.0 else arrayMs.toFloat / listMs.toFloat
  IO.println s!"{label}: List {listMs}ms, Array {arrayMs}ms, ratio {ratio} (check: {r1 == r2})"

def main : IO Unit := do
  let n := 2000000
  IO.println s!"n = {n}"
  IO.println ""

  -- Random Nat
  let randomList ← (List.range n).mapM (fun _ => IO.rand 0 1000)
  let randomArray := randomList.toArray
  bench "Random Nat       " (sortListNat randomList) (sortArrayNat randomArray)

  -- Reversed Nat
  let revList := (List.range' 1 n).reverse
  let revArray := revList.toArray
  bench "Reversed Nat     " (sortListNat revList) (sortArrayNat revArray)

  -- Sorted Nat
  let sortedList := List.range n
  let sortedArray := sortedList.toArray
  bench "Sorted Nat       " (sortListNat sortedList) (sortArrayNat sortedArray)

  -- All same Nat
  let sameList := List.replicate n 42
  let sameArray := sameList.toArray
  bench "All same Nat     " (sortListNat sameList) (sortArrayNat sameArray)

  -- Two distinct values
  let twoValList ← (List.range n).mapM (fun _ => do let r ← IO.rand 0 1; return r)
  let twoValArray := twoValList.toArray
  bench "Two values Nat   " (sortListNat twoValList) (sortArrayNat twoValArray)

  -- Random with large range
  let bigRandList ← (List.range n).mapM (fun _ => IO.rand 0 n)
  let bigRandArray := bigRandList.toArray
  bench "Random large Nat " (sortListNat bigRandList) (sortArrayNat bigRandArray)

  -- Random UInt64
  let mut x : UInt64 := 1
  let mut y : UInt64 := 1
  let mut u64Arr : Array UInt64 := Array.emptyWithCapacity n
  for _ in *...(n : Nat) do
    x := x * 829382384382829 + y
    y := y + 1
    u64Arr := u64Arr.push x
  let u64List := u64Arr.toList
  bench "Random UInt64    " (sortListUInt64 u64List) (sortArrayUInt64 u64Arr)

  IO.println ""
  IO.println "(ratio > 1 means List faster, < 1 means Array faster)"
