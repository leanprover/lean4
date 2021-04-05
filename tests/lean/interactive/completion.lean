structure Foo where
  foo : Nat

example (f : Foo) : f.
                    --^ textDocument/completion
example : Nat := 0  -- recover

example (f : Foo) : f.f
                     --^ textDocument/completion
example : Nat := 0  -- recover

example (f : Foo) : id f |>.
                          --^ textDocument/completion
example : Nat := 0  -- recover

example (f : Foo) : id f |>.f
                           --^ textDocument/completion
