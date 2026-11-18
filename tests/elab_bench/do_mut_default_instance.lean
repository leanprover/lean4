import Lean

/-!
Benchmark: a `do` block of `n` statements `if b i then xⱼ := xⱼ + i` over 20 variables declared
as `let mut xⱼ := 0`. The type of every `xⱼ` stays a metavariable until the default instance for
`OfNat` applies at the end of the block, so every join point has metavariables in its type and
every `+` waits for the default instance.
-/

open Lean Elab Command

def mkInput (n : Nat) : String := Id.run do
  let vars := (List.range 20).map (s!"x{·}")
  let mut s := "set_option maxRecDepth 100000 in\n\
    noncomputable def f (b : Nat → Bool) : StateM Nat Nat := do\n"
  for v in vars do
    s := s ++ s!"  let mut {v} := 0\n"
  for i in [0:n] do
    s := s ++ s!"  if b {i} then x{i % 20} := x{i % 20} + {i}\n"
  return s ++ s!"  pure ({" + ".intercalate vars})\n"

elab "#bench" : command => do
  let n := if (← IO.getEnv "TEST_BENCH") == some "1" then 60 else 5
  match Parser.runParserCategory (← getEnv) `command (mkInput n) with
  | .ok stx => elabCommand stx
  | .error e => throwError e

#bench
