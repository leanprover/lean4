
def foo1(bar : Nat) : Bool := true
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

example : Nat := Id.run do
  let mut x := 1
  x := 2
  x
--^ textDocument/documentHighlight

example : Nat := Id.run do
  let mut y : Nat := 0
  for x in [0] do
    y := y + x
  if true then
    y := y + 1
  else
    return y
  pure y
     --^ textDocument/documentHighlight

example : Nat := Id.run do
  let mut y := 0
  if true then
    y := 1
  return y  -- TODO: definition should be first `y`
       --^ textDocument/documentHighlight

example (x : Option Nat) : Nat :=
  match x with
  | some x => 1
       --^ textDocument/documentHighlight
  | none   => 0

/-!
A helper term info node accidentally led to this highlight including `by` (and "go to definition"
jumping to `rfl` in full projects).
-/
example : True := by
  simp
--^ textDocument/documentHighlight
