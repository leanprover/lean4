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

Results are reported per-pattern and in aggregate.
-/

open List.MergeSort.Internal

@[noinline]
def sortList (xs : List Nat) : IO Nat := return (mergeSortTR₂ xs).length

@[noinline]
def sortArray (xs : Array Nat) : IO Nat := return xs.mergeSort.size

def benchOne (label : String) (listInput : List Nat) (arrayInput : Array Nat) (n : Nat) :
    IO (Nat × Nat) := do
  let start ← IO.monoMsNow
  let r1 ← sortList listInput
  let mid ← IO.monoMsNow
  let r2 ← sortArray arrayInput
  let done ← IO.monoMsNow
  if r1 != n || r2 != n then
    throw <| IO.userError s!"{label}: correctness check failed"
  let listMs := mid - start
  let arrayMs := done - mid
  let ratio := if listMs == 0 then 0.0 else arrayMs.toFloat / listMs.toFloat
  IO.println s!"  {label}: List {listMs}ms, Array {arrayMs}ms, ratio {ratio}"
  return (listMs, arrayMs)

def main (args : List String) : IO Unit := do
  let k := 5
  let some arg := args[0]? | throw <| IO.userError s!"Usage: mergeSort <N>\nSorts N * 10^{k} elements"
  let some i := arg.toNat? | throw <| IO.userError s!"Invalid argument: expected positive integer"
  let n := i * (10^k)

  IO.println s!"Benchmarking mergeSort with n={n} ({i} * 10^{k})"
  IO.println ""

  -- Generate test inputs (Lists)
  let reversed := (List.range' 1 n).reverse
  let sorted := List.range n
  let random ← (List.range n).mapM (fun _ => IO.rand 0 1000)
  let partiallySorted := (List.range (i * (10^(k-3)))).flatMap (fun k =>
    (k * 1000 + 1) :: (k * 1000) :: List.range' (k * 1000 + 2) 998)

  -- Per-pattern benchmarks
  IO.println "Per-pattern results:"
  let (lt1, at1) ← benchOne "Reversed        " reversed reversed.toArray n
  let (lt2, at2) ← benchOne "Sorted          " sorted sorted.toArray n
  let (lt3, at3) ← benchOne "Random          " random random.toArray n
  let (lt4, at4) ← benchOne "Partially sorted" partiallySorted partiallySorted.toArray n

  -- Aggregate
  let listTotal := lt1 + lt2 + lt3 + lt4
  let arrayTotal := at1 + at2 + at3 + at4
  IO.println ""
  IO.println s!"Aggregate (4 cases):"
  IO.println s!"  List.mergeSort:  {listTotal} ms total, {listTotal/4} ms average"
  IO.println s!"  Array.mergeSort: {arrayTotal} ms total, {arrayTotal/4} ms average"
  IO.println ""

  IO.println "Comparison:"
  if arrayTotal < listTotal then
    let speedup := listTotal.toFloat / arrayTotal.toFloat
    IO.println s!"  Array.mergeSort is {speedup}x faster overall"
  else if listTotal < arrayTotal then
    let speedup := arrayTotal.toFloat / listTotal.toFloat
    IO.println s!"  List.mergeSort is {speedup}x faster overall"
  else
    IO.println "  Both implementations took the same time"

  IO.println ""
  IO.println "(ratio > 1 means List faster, < 1 means Array faster)"
