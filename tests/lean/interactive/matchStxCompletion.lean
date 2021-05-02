structure C where
  f1 : Nat
  f2 : Bool
  b1 : String

def f (x : Lean.Syntax) (y : C) : IO Nat := do
  match x with
  | `($a + 1) =>
    if y.
       --^ textDocument/completion
