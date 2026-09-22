import Lean

/-!
Benchmark: cost of realizing constants (here, equation lemmas) in a file with many realizations.

Every `realizeConst` call replays the changes it made to the environment extensions onto the
kernel environment, and all replays of a file run serially on the `checked` task chain. The replay
of an extension must therefore cost only the entries added by that realization, not the entries the
extension accumulated in the whole file, otherwise the total cost is quadratic in the number of
realizations and shows up as the elaboration thread waiting for the chain.

The input is `n` pairs of a structurally recursive definition and a theorem proved by `induction`
and `simp only [f]`, so every theorem realizes the equation lemmas of a fresh definition. The time
for `2n` pairs should be about twice the time for `n` pairs.
-/

open Lean Elab

/-- `n` pairs of a structural definition and a theorem that realizes its equation lemmas. -/
def mkInput (n : Nat) : String := Id.run do
  let mut s := ""
  for i in [0:n] do
    s := s ++ s!"def f{i} : Nat → Nat\n  | 0 => 0\n  | n+1 => f{i} n + 1\n"
    s := s ++ s!"theorem t{i} (n : Nat) : f{i} n = n := by\n"
    s := s ++ s!"  induction n with\n  | zero => simp only [f{i}]\n  | succ n ih => simp only [f{i}, ih]\n"
  return s

def runBench (n : Nat) : IO Unit := do
  let input := mkInput n
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := `Init }] {} (loadExts := true)
  let opts := internal.cmdlineSnapshots.set {} true
  let opts := Elab.async.set opts true
  let t0 ← IO.monoMsNow
  let (_, msgs) ← Lean.Elab.process input env opts
  let t1 ← IO.monoMsNow
  if msgs.hasErrors then
    for msg in msgs.toArray do
      IO.println (← msg.toString)
    throw <| IO.userError "unexpected errors"
  IO.println s!"measurement: realize_{n} {(t1 - t0).toFloat / 1000.0} s"

#eval show IO Unit from do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  if bench then
    runBench 2000
    runBench 4000
  else
    runBench 100
