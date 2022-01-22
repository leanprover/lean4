
def foo1(bar : Nat) : Nat := 3
                     --^ textDocument/documentHighlight

#eval foo1 2
#eval foo1 3
     --^ textDocument/documentHighlight

def foo2 : Nat :=
  let bar := 2
  bar + 3
 --^ textDocument/documentHighlight

structure Baz where
  bar : Nat
  bar' : Nat
 --^ textDocument/documentHighlight

def foo3 (baz : Baz) : Nat :=
  baz.bar
     --^ textDocument/documentHighlight

def foo4 (bar : Nat) : Baz :=
  { bar := bar, bar' := bar }
   --^ textDocument/documentHighlight
          --^ textDocument/documentHighlight
