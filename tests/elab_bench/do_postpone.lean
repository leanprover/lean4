import Lean

/-!
Benchmark: a `do` block of `n` pairs `let pᵢ ← pure ⟨i, i⟩; let _qᵢ : Nat × Nat := pᵢ`.
The anonymous constructor in every `pᵢ` postpones until the next statement fixes the type of `pᵢ`.
-/

open Lean Elab Command

def mkInput (n : Nat) : String := Id.run do
  let mut s := "set_option maxRecDepth 100000 in\n\
    noncomputable def f : StateM Nat (Nat × Nat) := do\n"
  for i in [0:n] do
    s := s ++ s!"  let p{i} ← pure ⟨{i}, {i}⟩\n  let _q{i} : Nat × Nat := p{i}\n"
  return s ++ s!"  pure p{n-1}\n"

elab "#bench" : command => do
  let n := if (← IO.getEnv "TEST_BENCH") == some "1" then 60 else 5
  match Parser.runParserCategory (← getEnv) `command (mkInput n) with
  | .ok stx => elabCommand stx
  | .error e => throwError e

#bench
