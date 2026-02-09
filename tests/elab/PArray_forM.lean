import Lean.Data.PersistentArray
/-!
Test `PersistentArray.forM` with nonzero start position.
-/

def mk (n : Nat) : Lean.PersistentArray Nat :=
  List.range n |>.toPArray'

def sum1 (start : Nat) (s : List Nat) : Nat :=
  let (_, s) := StateT.run (m := Id) (s.drop start |>.forM fun val => modify (· + val)) 0
  s

def sum2 (start : Nat) (s : Lean.PArray Nat) : Nat :=
  let (_, s) := StateT.run (m := Id)  (s.forM (start := start) (fun val => modify (· + val))) 0
  s

def check (s₁ : List Nat) : IO Unit := do
  let s₂ := s₁.toPArray'
  let n  := s₂.size
  for i in *...n do
    unless sum1 i s₁ == sum2 i s₂ do
      throw <| .userError "failed"
  IO.println "ok"

#eval check (List.range 10)
#eval check (List.range 0)
#eval check (List.range 2000)
#eval check (List.replicate 1000 1)
#eval check (List.replicate 10 2)
