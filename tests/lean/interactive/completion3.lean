structure S where
  x : Nat
  y : String
  b : Bool

def f (s : S) : Nat :=
  let rec foo (s : S) :=
    if s. then 1 else 2
       --^ textDocument/completion
  foo s
