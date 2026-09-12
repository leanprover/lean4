module

import Init.Data.Array.QSort

/-!
Regression tests for three-way partitioning in `Array.qsort` (#8087).
-/

public def main : IO Unit := do
  let repeated := (Array.replicate 100000 0).qsort
  unless repeated.size = 100000 && repeated[0]? = some 0 && repeated[99999]? = some 0 do
    throw <| .userError "sorting a constant array produced an incorrect result"

  let duplicateHeavy := #[3, 1, 2, 3, 2, 1, 3, 1, 2].qsort
  unless duplicateHeavy = #[1, 1, 1, 2, 2, 2, 3, 3, 3] do
    throw <| .userError "sorting duplicate-heavy input produced an incorrect result"

  let subrange := #[9, 3, 2, 1, 8].qsort (lo := 1) (hi := 3)
  unless subrange = #[9, 1, 2, 3, 8] do
    throw <| .userError "sorting a subrange changed the wrong elements"

  let reversed := #[4, 3, 2, 1].qsort (lo := 3) (hi := 1)
  unless reversed = #[4, 3, 2, 1] do
    throw <| .userError "sorting a reversed range changed the array"
