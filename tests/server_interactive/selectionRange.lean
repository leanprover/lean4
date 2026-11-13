/-!
Tests for `textDocument/selectionRange`. Verifies that selection ranges expand from
the cursor position outward through enclosing syntax nodes, for terms, tactics, and
type expressions.
-/

def ex1 : Nat := 1 + 2 * 3
                       --^ selectionRange

-- Cursor somewhere in the infix notation
def ex2 : Nat := 1 + 3
                  --^ selectionRange

def ex3 (x : Nat) : Nat := (x + 1) * 2
                          --^ selectionRange

def ex4 : Option (List Nat) := none
                  --^ selectionRange

theorem ex5 : 0 + 1 = 1 := by simp [Nat.zero_add]
                               --^ selectionRange

def ex6 : Nat :=
  let x := 10 * 2
            --^ selectionRange
  x
