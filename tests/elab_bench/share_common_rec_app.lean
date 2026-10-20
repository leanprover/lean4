import Lean

/-!
Benchmark: hash-consing of pre-definitions (`share common exprs`) on a file with many
recursive definitions.

Recursive calls are annotated with their `Syntax`. The annotated expressions are traversed by
`ShareCommon.shareCommon'`, which visits every object reachable from them. If the stored syntax
kept `SourceInfo.original` infos, every one of them would point at the whole input string, and
each recursive call would cost a hash of the whole file. The total would then be quadratic in
the file size.

The input is generated as a string and elaborated with `Lean.Elab.process`, so the source infos
point at the generated input, not at this file. The input ends with a large comment that makes
the input much bigger than the declarations themselves. If the cost depends on the input size,
the padded run is much slower than the unpadded one.
-/

open Lean Elab

/--
`numDefs` structurally recursive definitions on a small inductive type, followed by a comment
of `padding` characters.
-/
def mkInput (numDefs padding : Nat) : String := Id.run do
  let mut s := "inductive N | Z | S (n : N)\n"
  for i in [0:numDefs] do
    s := s ++ s!"def g{i} : N → N\n  | .Z => .Z\n  | .S q => .S (g{i} q)\n"
  s := s ++ "/-\n" ++ "".pushn 'x' padding ++ "\n-/\n"
  return s

def runBench (numDefs padding : Nat) : CoreM Unit := do
  let input := mkInput numDefs padding
  let t0 ← IO.monoMsNow
  let (_, msgs) ← Lean.Elab.process input (← getEnv) {}
  let t1 ← IO.monoMsNow
  if msgs.hasErrors then
    for msg in msgs.toArray do
      IO.println (← msg.toString)
    throwError "unexpected errors"
  IO.println s!"measurement: defs_{numDefs}_pad_{padding} {(t1 - t0).toFloat / 1000.0} s"

#eval show CoreM Unit from do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  if bench then
    runBench 2000 0
    runBench 2000 4000000
  else
    runBench 20 100000
