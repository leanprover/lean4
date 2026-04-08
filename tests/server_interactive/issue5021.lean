example : False := by
  refine ?_
       --^ textDocument/hover
        --^ textDocument/hover
  sorry

example : False := by
  refine ? _ -- check that a space is allowed
       --^ textDocument/hover
         --^ textDocument/hover
  sorry
