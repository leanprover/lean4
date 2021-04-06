structure S where
  fn1 : Nat → IO Unit
  fn2 : Bool → IO Unit
  pred : String → Bool

def f (s : S) : IO Unit := do
  s.fn1 10
  s.
  --^ textDocument/completion

def g1 (s : S) : IO Unit := do
  if (← s.
        --^ textDocument/completion

def g2 (s : S) : IO Unit := do
  s.fn1 10
  if (← s.f
         --^ textDocument/completion

def g3 (s : S) : IO String := do
  let mut x := 1 + s.
                   --^ textDocument/completion
