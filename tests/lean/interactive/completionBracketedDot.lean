inductive Direction where
  | up
  | right
  | down
  | left

-- It would be nice if this actually provided `up`, `right`, `down` and `left` in the future
def foo : Direction :=
  (.)
  --^ textDocument/completion
