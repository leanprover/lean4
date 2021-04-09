structure C where
  f1 : Nat
  f2 : Bool
  b1 : String

structure D extends C where
  f3 : Bool

def f (c : D) : IO Unit :=
  visit c
where
  visit (c : D) : IO Unit :=
    let x := c.
             --^ textDocument/completion

abbrev E := D

def E.doubleF1 (e : E) :=
  e.f1 + e.f1

def g (e : E) :=
  e.
  --^ textDocument/completion
