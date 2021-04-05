structure Foo where
  foo : Nat

example (f : Foo) : f.
                    --^ textDocument/completion
example (f : Foo) : f.f
                     --^ textDocument/completion
example (f : Foo) : id f |>.
                          --^ textDocument/completion
example (f : Foo) : id f |>.f
                           --^ textDocument/completion
