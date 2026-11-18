import Lean

/-!
Benchmark: a `do` block of `n` statements `if b i then xⱼ := xⱼ + i` over 20 `let mut` variables
of type `Nat`. Every `if` has a continuation, so every `if` introduces a join point whose
parameters are the reassigned variables.
-/

open Lean Elab Command

def mkInput (n : Nat) : String := Id.run do
  let vars := (List.range 20).map (s!"x{·}")
  let mut s := "set_option maxRecDepth 100000 in\n\
    noncomputable def f (b : Nat → Bool) : StateM Nat Nat := do\n"
  for v in vars do
    s := s ++ s!"  let mut {v} : Nat := 0\n"
  for i in [0:n] do
    s := s ++ s!"  if b {i} then x{i % 20} := x{i % 20} + {i}\n"
  return s ++ s!"  pure ({" + ".intercalate vars})\n"

elab "#bench" : command => do
  let n := if (← IO.getEnv "TEST_BENCH") == some "1" then 400 else 10
  match Parser.runParserCategory (← getEnv) `command (mkInput n) with
  | .ok stx => elabCommand stx
  | .error e => throwError e

#bench
