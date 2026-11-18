import Lean

/-!
Benchmark: two families of nested actions `(← …)` in a single `let`.
* `flat`: `let r := (← a) + (← a) + … + (← a)` with `n` actions side by side.
* `deep`: `let r := (← g (← g (… (← g 0))))` with `n` actions nested in each other.
-/

open Lean Elab Command

def a : StateM Nat Nat := get

def g (x : Nat) : StateM Nat Nat := pure (x + 1)

def mkFlat (n : Nat) : String :=
  "set_option maxRecDepth 100000 in\nnoncomputable def flat : StateM Nat Nat := do\n  let r := " ++
    " + ".intercalate (List.replicate n "(← a)") ++ "\n  pure r\n"

def mkDeep (n : Nat) : String :=
  "set_option maxRecDepth 100000 in\nnoncomputable def deep : StateM Nat Nat := do\n  let r := " ++
    "".intercalate (List.replicate n "(← g ") ++ "0" ++ "".pushn ')' n ++ "\n  pure r\n"

elab "#bench" : command => do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  for input in [mkFlat (if bench then 400 else 10), mkDeep (if bench then 800 else 10)] do
    match Parser.runParserCategory (← getEnv) `command input with
    | .ok stx => elabCommand stx
    | .error e => throwError e

#bench
