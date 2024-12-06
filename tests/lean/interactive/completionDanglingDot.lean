-- Regression test for a bug where the dangling dot was not accounted for in some
-- atomic completions, which lead to invalid completions after a dangling dot

def foo : Unit :=
  x.  -- No completions expected
  --^ textDocument/completion

def bar : Array Nat := Id.run do
  let mut x := sorry
  let foo := x.  -- No completions expected
             --^ textDocument/completion
  sorry
