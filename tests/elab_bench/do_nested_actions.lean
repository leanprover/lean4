import Lean

/-!
Benchmark: two families of nested actions `(← …)` in a single `let`.
* `flat`: `let r := (← a) + (← a) + … + (← a)` with `n` actions side by side.
* `deep`: `let r := (← g (← g (… (← g 0))))` with `n` actions nested in each other.
-/

open Lean Elab Command

set_option maxRecDepth 100000

def a : StateM Nat Nat := get

def g (x : Nat) : StateM Nat Nat := pure (x + 1)

elab "#bench" : command => do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let first ← `((← a))
  let flat ← (Array.range ((if bench then 400 else 10) - 1)).foldlM (init := first)
    fun t _ => `($t + (← a))
  elabCommand (← `(noncomputable def $(mkIdent `flat) : StateM Nat Nat := do
    let r := $flat
    pure r))
  let zero ← `(0)
  let deep ← (Array.range (if bench then 800 else 10)).foldlM (init := zero)
    fun t _ => `((← g $t))
  elabCommand (← `(noncomputable def $(mkIdent `deep) : StateM Nat Nat := do
    let r := $deep
    pure r))

#bench
