example (x y : Nat) (h : x = y) : y = x := by exact h.symm
                                                     --^ textDocument/hover
                                                  --^ textDocument/hover

example (x y : Nat) (h : x = y) : y = x := h.symm
                                            --^ textDocument/hover

example (x y : Nat) (h : x = y) : y = x := by exact (Eq.symm (Eq.symm h.symm))
                                                    --^ textDocument/hover
                                                               --^ textDocument/hover
                                                                    --^ textDocument/hover
                                                                      --^ textDocument/hover
