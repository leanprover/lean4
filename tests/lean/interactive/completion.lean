structure Foo where
  foo : Nat

example (g : Foo) : g.
                    --^ textDocument/completion
example (g : Foo) : g.f
                     --^ textDocument/completion
example (g : Foo) : id g |>.
                          --^ textDocument/completion
example (g : Foo) : id g |>.f
                           --^ textDocument/completion
