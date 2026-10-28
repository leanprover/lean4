/-!
Test for https://github.com/leanprover/lean4/issues/13858

Repeating `pure ()`s should scale linearly.
-/

set_option backward.do.legacy false

set_option maxHeartbeats 1000

def test : IO Unit := do
  pure () -- 1
  pure () -- 2
  pure () -- 3
  pure () -- 4
  pure () -- 5
  pure () -- 6
  pure () -- 7
  pure () -- 8
  pure () -- 9
  pure () -- 10
  pure () -- 11
  pure () -- 12
  pure () -- 13
  pure () -- 14
  pure () -- 15
  pure () -- 16
  pure () -- 17
  pure () -- 18
  pure () -- 19
  pure () -- 20
