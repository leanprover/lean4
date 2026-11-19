set_option backward.do.legacy false

def test : IO Unit := do
  for h : i in [1, 2, 3] do
    --^ textDocument/hover
        --^ textDocument/hover
    pure ()
