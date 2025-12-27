import Lean.Elab.Parallel

/-!
# Tests for chunked parallel execution

Tests for the chunking support in `Lean.Elab.Parallel`.
-/

open Lean Core

/-! ## CoreM tests -/

/-- Test that par with maxTasks=0 (default) works like original -/
def testCoreMParDefault : CoreM Unit := do
  let jobs := (List.range 10).map fun i => pure i
  let results ← CoreM.par jobs
  let values := results.filterMap fun r =>
    match r with
    | .ok (v, _) => some v
    | .error _ => none
  assert! values == List.range 10

/-- Test that par with chunking produces same results -/
def testCoreMParChunked : CoreM Unit := do
  let jobs := (List.range 20).map fun i => pure i
  let results ← CoreM.par jobs (maxTasks := 4) (minChunkSize := 2)
  let values := results.filterMap fun r =>
    match r with
    | .ok (v, _) => some v
    | .error _ => none
  -- Results should be in original order
  assert! values == List.range 20

/-- Test that par' with chunking works -/
def testCoreMPar'Chunked : CoreM Unit := do
  let jobs := (List.range 15).map fun i => pure (i * 2)
  let results ← CoreM.par' jobs (maxTasks := 3) (minChunkSize := 2)
  let values := results.filterMap fun r =>
    match r with
    | .ok v => some v
    | .error _ => none
  assert! values == (List.range 15).map (· * 2)

/-- Test error handling in chunks -/
def testCoreMParChunkedErrors : CoreM Unit := do
  let jobs := (List.range 10).map fun i =>
    if i == 5 then throwError "error at 5"
    else pure i
  let results ← CoreM.par' jobs (maxTasks := 3) (minChunkSize := 2)
  -- Should have 9 successes and 1 error
  let successes := results.filter fun r => match r with | .ok _ => true | .error _ => false
  let errors := results.filter fun r => match r with | .ok _ => false | .error _ => true
  assert! successes.length == 9
  assert! errors.length == 1

#eval do
  let env ← importModules #[{ module := `Init }] {} 0
  let (_, _) ← testCoreMParDefault.toIO { fileName := "", fileMap := default } { env }
  IO.println "testCoreMParDefault passed"

#eval do
  let env ← importModules #[{ module := `Init }] {} 0
  let (_, _) ← testCoreMParChunked.toIO { fileName := "", fileMap := default } { env }
  IO.println "testCoreMParChunked passed"

#eval do
  let env ← importModules #[{ module := `Init }] {} 0
  let (_, _) ← testCoreMPar'Chunked.toIO { fileName := "", fileMap := default } { env }
  IO.println "testCoreMPar'Chunked passed"

#eval do
  let env ← importModules #[{ module := `Init }] {} 0
  let (_, _) ← testCoreMParChunkedErrors.toIO { fileName := "", fileMap := default } { env }
  IO.println "testCoreMParChunkedErrors passed"

/-! ## All tests passed -/

#eval IO.println "All parallel_chunked tests passed!"
