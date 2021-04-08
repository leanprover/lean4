structure C where
  f1 : Nat
  f2 : Bool
  b1 : String

def f (c : C) : IO Unit :=
  visit c
where
  visit (c : C) : IO Unit :=
    let x := c.
             --^ textDocument/completion
