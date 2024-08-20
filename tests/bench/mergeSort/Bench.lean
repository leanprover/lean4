open List.MergeSort.Internal

def main (args : List String) : IO Unit := do
  let k := 5
  let some arg := args[0]? | throw <| IO.userError s!"specify length of test data in multiples of 10^{k}"
  let some i := arg.toNat? | throw <| IO.userError s!"specify length of test data in multiples of 10^{k}"
  let n := i * (10^k)
  let i₁ := List.iota n
  let i₂ := List.range n
  let i₃ ← (List.range n).mapM (fun _ => IO.rand 0 1000)
  let i₄ := (List.range (i * (10^(k-3)))).bind (fun k => (k * 1000 + 1) :: (k * 1000) :: List.range' (k * 1000 + 2) 998)
  let start ← IO.monoMsNow
  let o₁ := (mergeSortTR₂ (· ≤ ·) i₁).length == n
  let o₂ := (mergeSortTR₂ (· ≤ ·) i₂).length == n
  let o₃ := (mergeSortTR₂ (· ≤ ·) i₃).length == n
  let o₄ := (mergeSortTR₂ (· ≤ ·) i₄).length == n
  IO.println (((← IO.monoMsNow) - start)/4)
  IO.Process.exit (if o₁ && o₂ && o₃ && o₄ then 0 else 1)
