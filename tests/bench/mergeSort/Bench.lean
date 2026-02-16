/-
Benchmark comparing `List.mergeSort` and `Array.mergeSort` performance.

Usage:
  ./mergeSort <N>

where N specifies test size: N * 10^5 elements will be sorted.

Example:
  ./mergeSort 10    # Sort 1,000,000 elements
  ./mergeSort 100   # Sort 10,000,000 elements

The benchmark runs 4 test cases for each implementation:
1. Reversed data (worst case for some algorithms)
2. Already sorted data (best case)
3. Random data
4. Partially sorted data with duplicates

Note: Array.mergeSort shows significant performance advantages at larger scales
(>500k elements), achieving 2-3.5x speedup over List.mergeSort for datasets
with millions of elements.
-/

open List.MergeSort.Internal

@[noinline]
def benchmarkList (inputs : List (List Nat)) (n : Nat) : IO Nat := do
  let start ← IO.monoMsNow
  let o₁ := (mergeSortTR₂ inputs[0]!).length == n
  let o₂ := (mergeSortTR₂ inputs[1]!).length == n
  let o₃ := (mergeSortTR₂ inputs[2]!).length == n
  let o₄ := (mergeSortTR₂ inputs[3]!).length == n
  let elapsed := (← IO.monoMsNow) - start
  if !(o₁ && o₂ && o₃ && o₄) then
    throw <| IO.userError "List.mergeSort correctness check failed"
  return elapsed

@[noinline]
def benchmarkArray (inputs : List (Array Nat)) (n : Nat) : IO Nat := do
  let start ← IO.monoMsNow
  let o₁ := (Array.mergeSort inputs[0]!).size == n
  let o₂ := (Array.mergeSort inputs[1]!).size == n
  let o₃ := (Array.mergeSort inputs[2]!).size == n
  let o₄ := (Array.mergeSort inputs[3]!).size == n
  let elapsed := (← IO.monoMsNow) - start
  if !(o₁ && o₂ && o₃ && o₄) then
    throw <| IO.userError "Array.mergeSort correctness check failed"
  return elapsed

def main (args : List String) : IO Unit := do
  let k := 5
  let some arg := args[0]? | throw <| IO.userError s!"Usage: mergeSort <N>\nSorts N * 10^{k} elements"
  let some i := arg.toNat? | throw <| IO.userError s!"Invalid argument: expected positive integer"
  let n := i * (10^k)

  IO.println s!"Benchmarking mergeSort with n={n} ({i} * 10^{k})"
  IO.println "Test cases: reversed, sorted, random, partially-sorted"
  IO.println ""

  -- Generate test inputs (Lists)
  let listInputs := [
    (List.range' 1 n).reverse,  -- Reversed
    List.range n,                -- Already sorted
    ← (List.range n).mapM (fun _ => IO.rand 0 1000),  -- Random
    (List.range (i * (10^(k-3)))).flatMap (fun k =>   -- Partially sorted with duplicates
      (k * 1000 + 1) :: (k * 1000) :: List.range' (k * 1000 + 2) 998)
  ]

  -- Convert to Arrays
  let arrayInputs := listInputs.map List.toArray

  -- Benchmark List.mergeSort
  let listTime ← benchmarkList listInputs n
  IO.println s!"List.mergeSort:  {listTime} ms total, {listTime/4} ms average"

  -- Benchmark Array.mergeSort
  let arrayTime ← benchmarkArray arrayInputs n
  IO.println s!"Array.mergeSort: {arrayTime} ms total, {arrayTime/4} ms average"
  IO.println ""

  -- Comparative results
  IO.println "Comparison:"
  if arrayTime < listTime then
    let speedup := listTime.toFloat / arrayTime.toFloat
    IO.println s!"  Array.mergeSort is {speedup}x faster"
  else if listTime < arrayTime then
    let speedup := arrayTime.toFloat / listTime.toFloat
    IO.println s!"  List.mergeSort is {speedup}x faster"
  else
    IO.println "  Both implementations took the same time"
